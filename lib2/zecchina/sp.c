/*
    Copyright 2002 Alfredo Braunstein, Michele Leone, Marc Mézard, 
                   Martin Weigt and Riccardo Zecchina

    This file is part of SP (Survey Propagation).

    SP is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or 
    (at your option) any later version.

    SP is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with SP; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <setjmp.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include "random.h"
#include "formula.h"
#include "sp.h"

#ifdef QUEUE

#include "queue.h"

#endif //QUEUE

//global system vars & structures
struct vstruct *v=NULL; //all per var information
struct clausestruct *clause=NULL; //all per clause information
double *magn=NULL; //spin magnetization list (for fixing ordering)
int *perm=NULL; //permutation, for update ordering
int M=0; //number of clauses
int N=0; //number of variables
int *ncl=NULL; //clause size histogram
int maxlit=0; //maximum clause size
int freespin; //number of unfixed variables
double epsilon=EPSILONDEF; //convergence criterion
int maxconn=0; //maximum connectivity

//auxiliary vars
int *list=NULL;
double *prod=NULL;

//flags & options
double percent=0;
int fixperstep=1;
int ndanger=0;
int generate=0;
int verbose=0;
int fields=0;
int stop=0;
int complexity=0;
FILE *paraplot=NULL;
FILE *replay=NULL;
char *load=NULL;
int iterations=ITERATIONS;
int K=3;
int uselazy=0;
double rho=0;
double norho=1;

jmp_buf contradiction;

#define EPS (1.0e-16)

// written by Hinata Yanagi (2019/02/24)
void load_formula(value ml_cnf) {
	CAMLparam1(ml_cnf);
	CAMLlocal3(ml_clauses, ml_clause, ml_literals);

	int variable, m, n, lit_per_clause;

	for (ml_clause = ml_cnf; ml_clause != Val_emptylist; ml_clause = Field(ml_clause, 1)) {
		lit_per_clause = 0;

		for (
			ml_literals = Field(Field(ml_clause, 0), 0);
			ml_literals != Val_emptylist;
			ml_literals = Field(ml_literals, 1))
		{
			variable = Int_val(Field(ml_literals, 0));
			if (variable > N) N = variable;
			lit_per_clause++;
		}

		for (
			ml_literals = Field(Field(ml_clause, 0), 1);
			ml_literals != Val_emptylist;
			ml_literals = Field(ml_literals, 1))
		{
			variable = Int_val(Field(ml_literals, 0));
			if (variable > N) N = variable;
			lit_per_clause++;
		}

		if (lit_per_clause > maxlit) {
			maxlit = lit_per_clause;
		}

		M++;
	}

	N++;

	clause = calloc(M, sizeof(struct clausestruct));
	v = calloc(N + 1, sizeof(struct vstruct));
	ncl = calloc(maxlit + 1, sizeof(int));

	for (ml_clause = ml_cnf; ml_clause != Val_emptylist; ml_clause = Field(ml_clause, 1)) {
		for (
			ml_literals = Field(Field(ml_clause, 0), 0);
			ml_literals != Val_emptylist;
			ml_literals = Field(ml_literals, 1))
		{
			variable = Int_val(Field(ml_literals, 0));
			v[variable].clauses++;
		}

		for (
			ml_literals = Field(Field(ml_clause, 0), 1);
			ml_literals != Val_emptylist;
			ml_literals = Field(ml_literals, 1))
		{
			variable = Int_val(Field(ml_literals, 0));
			v[variable].clauses++;
		}
	}

	for(variable = 0; variable < N; variable++) {
		if(v[variable].clauses) {
			v[variable].clauselist = calloc(v[variable].clauses, sizeof(struct clauselist));
			v[variable].clauses = 0;
		}
	}

	for (ml_clause = ml_cnf, m = 0; ml_clause != Val_emptylist; ml_clause = Field(ml_clause, 1), m++) {
		for (
			ml_literals = Field(Field(ml_clause, 0), 0);
			ml_literals != Val_emptylist;
			ml_literals = Field(ml_literals, 1)) clause[m].lits++;

		for (
			ml_literals = Field(Field(ml_clause, 0), 1);
			ml_literals != Val_emptylist;
			ml_literals = Field(ml_literals, 1)) clause[m].lits++;

		clause[m].literal = calloc(clause[m].lits, sizeof(struct literalstruct));
		n = 0;

		for (
			ml_literals = Field(Field(ml_clause, 0), 0);
			ml_literals != Val_emptylist;
			ml_literals = Field(ml_literals, 1))
		{
			variable = Int_val(Field(ml_literals, 0));
			v[variable].clauselist[v[variable].clauses].clause = &clause[m];
			v[variable].clauselist[v[variable].clauses++].lit = n;
			clause[m].literal[n].var = variable;
			clause[m].literal[n++].bar = 1;

			if (v[variable].clauses > maxconn) {
				maxconn = v[variable].clauses;
			}
		}

		for (
			ml_literals = Field(Field(ml_clause, 0), 1);
			ml_literals != Val_emptylist;
			ml_literals = Field(ml_literals, 1))
		{
			variable = Int_val(Field(ml_literals, 0));
			v[variable].clauselist[v[variable].clauses].clause = &clause[m];
			v[variable].clauselist[v[variable].clauses++].lit = n;
			clause[m].literal[n].var = variable;
			clause[m].literal[n++].bar = 0;

			if (v[variable].clauses > maxconn) {
				maxconn = v[variable].clauses;
			}
		}

		clause[m].type = clause[m].lits = n;
		ncl[n]++;
	}

	freespin = N;
}

// written by Hinata Yanagi (2019/02/24)
CAMLprim value solve(value ml_cnf, value ml_buffer)
{
	CAMLparam1(ml_cnf);

	int oldfreespin, variable, m;

	v=NULL; //all per var information
	clause=NULL; //all per clause information
	magn=NULL; //spin magnetization list (for fixing ordering)
	perm=NULL; //permutation, for update ordering
	M=0; //number of clauses
	N=0; //number of variables
	ncl=NULL; //clause size histogram
	maxlit=0; //maximum clause size
	maxconn=0; //maximum connectivity

	//auxiliary vars
	list=NULL;
	prod=NULL;

	if (setjmp(contradiction) == 1) {
		fprintf(stderr, "CONTRADICTION\n");
		goto FINAL;
	}

	usrand(0);

//read or generate a formula
	load_formula(ml_cnf);
//define fixperstep if based on percent
	if(percent) {
		fixperstep=N*percent/100.0;
	}
//allocate mem for dynamics
	initmem();
//possibly simplify the formula
	oneclauses();
//pick an initial starting point for the dynamics
	randomize_eta();
//a first normal convergence helps
	if(uselazy)
		sequential_converge();
//fix ndanger balanced spins (useful for restarts)
	while(ndanger--){
		if(!converge())
			goto FINAL;
		if (build_list(&index_pap)) goto FOUND;
		oldfreespin=freespin;
		fix_chunk(1);
		fprintf(stderr, "fixed %i PAP var (+%i ucp)\n",1,oldfreespin-freespin-1);
	}
//converge and fix fixperstep spins at a time
	while(converge()) {
		if(complexity)
			compute_sigma();
		oldfreespin=freespin;
		if (build_list(&index_biased)) goto FOUND;
		if(fields)
			print_fields();
		if(stop)
			goto FINAL;
		fix_chunk(fixperstep);
		if(ncl[0]==M)
			goto FOUND;
		fprintf(stderr, "fixed %i biased var%s (+%i ucp)\n",fixperstep,fixperstep>1?"s":"",oldfreespin-freespin-fixperstep);
		if(verbose)
			print_stats();
	}

	goto FINAL;

FOUND:
	fprintf(stderr, "FOUND\n");

	for(variable = 0; variable < N; variable++){
		Store_field(ml_buffer, variable, Val_int(v[variable].spin));
	}

FINAL:
	free(perm);
	free(list);
	free(magn);
	free(prod);

	for (m = 0; m < M; m++) {
		free(clause[m].literal);
	}

	for (variable = 0; variable < N; variable++) {
		free(v[variable].clauselist);
	}

	free(clause);
	free(v);
	free(ncl);

	CAMLreturn(Val_unit);
}

void oneclauses()
//initially simplify the formula, eliminating all 1-clauses 
{
	int c,var;
	for(c=0; c<M; c++) { 
		if(clause[c].lits==1) {
			var=clause[c].literal[0].var;
			if(v[var].spin==0) {
				fprintf(stderr, "eliminating var %i (in 1-clause)\n",var);
				fix(var,clause[c].literal[0].bar?-1:1);
			}
		}
	}
}

int parsecommandline(int argc, char **argv)
//get command line parameters
{
	double alpha=0;
	char c;
	generate=0;
	usrand(1);
	while((c=getopt(argc, argv,
#ifdef QUEUE
			"z"
#endif
			"R:k:cN:M:r:n:m:a:s:d:hf:v%:e:p:l:F/i:"))!=-1) {
		switch (c) {
		case 'R':
			rho=atof(optarg);
			norho=1-rho;
			break;
		case 'z':
			uselazy=1;
			break;
		case 'l':
			load=optarg;
			break;
		case 'p':
			paraplot=fopen(optarg,"w+");
			break;
		case 'r':
			replay=fopen(optarg,"w+");
			break;
		case 'N':
		case 'n':
			N=atoi(optarg);
			break;
		case 'M':
		case 'm':
			M=atoi(optarg);
			break;
		case 'a':
			alpha=atof(optarg);
			break;
		case 'e':
			epsilon=atof(optarg);
			break;
		case 's':
			usrand(atoi(optarg));
			srand(atoi(optarg));
			break;
		case '/':
			stop=1;
			break;
		case 'k':
		case 'K':
			K=atoi(optarg);
			break;
		case 'v':
			verbose++;
			break;
		case 'F':
			fields=1;
			break;
		case 'f':
			fixperstep=atoi(optarg);
			break;
		case '%':
			percent=atof(optarg);
			break;
		case 'd':
			ndanger=atoi(optarg);
			break;
		case 'i':
			iterations=atoi(optarg);
			break;
		case 'c':
			complexity=1;
			break;
		case 'h':
		default:
			fprintf(stderr, "%s [options]\n"
				"\n"
				"  formula\n"
				"\t-n <numvars>\n"
				"\t-m <numclauses>\n"
				"\t-a <alpha>\n"
				"\t-R <rho>\t modified dynamics (0=sp, 1=bp)\n"
				"\t\t\t (real values inbetween may make sense)\n"
				"\t-l <filename>\t reads formula from file\n"
				"  solving\n"
				"\t-d <danger>\t fix this much PAP spins (experimental)\n"
				"\t-f <fixes>\t per step\n"
				"\t-%% <fixes>\t per step (%%)\n"
				"\t-e <error>\t criterion for convergence\n"
				"\t-z \t\t use lazy convergence instead of sequential\n"
#ifndef QUEUE
				"\t\t\t (unavaliable, recompile with -DQUEUE)\n"
#endif
				"\t-i <iter>\t maximum number of iterations until convergence\n"
				"  stats\n"
				"\t-p <filename>\t output a magneticity plot\n"
				"\t-r <filename>\t replay file\n"
				"\t-c \t\t computes complexity\n"
				"\t-F \t\t print fields\n"
				"\t-v \t\t increase verbosity\n"
				"  misc\n"
				"\t-s <seed>\t (0=use time, default=1)\n"
				"\t-/\t\t stop after first convergence\n"
				"\t-h\t\t this help\n",argv[0]);
			exit(-1);
		}
	}
	if(load && !N && !M && !alpha) {
		generate=0;
	} else if(N && alpha && !M) {
		M=N*alpha;
		generate=1;
	} else if(M && alpha && !N) {
		N=M/alpha;
		generate=1;
	} else if(M && N && alpha==0) {
		generate=1;
	} else {
		fprintf(stderr, "error: you have to specify exactly TWO of -n,-m and -a, or -l FILE (and then a formula is read from FILE)\n");
		exit(-1);
	}
	return 0;
}

inline struct weightstruct normalize(struct weightstruct H)
//normalize a triplet
{
	double norm;
	norm=H.m+H.z+H.p;
	H.m/=norm;
	H.p/=norm;
	H.z/=norm;
	return H;
}

int order(void const *a, void const *b)
//order relation for qsort, uses ranking in magn[]
{
	double aux;
	aux=magn[*((int *)b)]-magn[*((int *)a)];
	return aux<0?-1:(aux>0?1:0);
}

double index_biased(struct weightstruct H)
//most biased ranking
{
	return fabs(H.p-H.m);
}
double index_pap(struct weightstruct H)
//most biased with some fuss
{
	return fabs(H.p-H.m)+randreal()*0.1;
}

double index_para(struct weightstruct H)
//least paramagnetic ranking
{
	return H.z;
}

double index_frozen(struct weightstruct H)
//most paramagnetic ranking
{
	return -H.z;
}

double index_best(struct weightstruct H)
//min(H.p,H.m) ranking
{
	return -(H.p>H.m?H.m:H.p);
}

int build_list(double (* index)(struct weightstruct))
//build an ordered list with order *index which is one of index_?
{
	int var,totsites;
	struct weightstruct H;
	double summag;
	double maxmag;
	summag=0;
	totsites=0;
	for(var=1; var<=N; var++) if(v[var].spin==0) {
		H=compute_field(var);
		list[totsites++]=var;
		magn[var]=(*index)(H);
		maxmag=H.p>H.m?H.p:H.m;
		summag+=maxmag;
	}
	qsort(list, totsites, sizeof(int), &order);
	fprintf(stderr, "<bias>:%f\n",summag/totsites);
	if(paraplot) {
		fprintf(paraplot,"%f %f %i %i %i\n", (N-freespin)*1.0/N, summag/totsites, freespin, ncl[2], ncl[3]);
		fflush(paraplot);
	}
	if(summag/totsites<PARAMAGNET) {
		fprintf(stderr, "paramagnetic state\n");
		fprintf(stderr, "sub-formula has:\n");
		print_stats();
		return 1;
	}
	return 0;
}

void randomize_eta()
//pick initial random values
{
	int i,j;
	for(i=0; i<M; i++) {
		for(j=0; j<clause[i].lits;j++) {
			clause[i].literal[j].eta=randreal();
		}
	}
}

void initmem()
//allocate mem (can be called more than once)
{
	free(perm);
	free(list);
	free(magn);
	free(prod);
	perm=calloc(M,sizeof(int));
	list=calloc(N+1,sizeof(int));
	magn=calloc(N+1,sizeof(double));
	prod=calloc(maxlit,sizeof(double));
#ifdef QUEUE
	queue_init(M);
#endif //QUEUE
	if(!perm||!list||!magn ||!prod){
		fprintf(stderr, "Not enough memory for internal structures\n");
		exit(-1);
	}
}

void compute_pi()
//compute pi products of all vars from scratch
{
	int i,var;
	struct clauselist *cl;
	struct literalstruct *l;
	for(var=1; var<=N; ++var) if(v[var].spin==0) {
		v[var].pi.p=1;
		v[var].pi.m=1;
#ifndef FAST_ITERATION
		v[var].pi.pzero=0;
		v[var].pi.mzero=0;
#endif
		for(i=0,cl=v[var].clauselist;i<v[var].clauses; i++,cl++) if(cl->clause->type) {
			l=cl->clause->literal+cl->lit;
			if(l->bar) {
#ifdef FAST_ITERATION
				v[var].pi.p*=1-l->eta;
#else
				if(1-l->eta>EPS) {
					v[var].pi.p*=1-l->eta;
				} else {
					v[var].pi.pzero++;
				}
#endif
			} else {
#ifdef FAST_ITERATION
				v[var].pi.m*=1-l->eta;
#else
				if(1-l->eta>EPS) {
					v[var].pi.m*=1-l->eta;
				} else {
					v[var].pi.mzero++;
				}
#endif				
			}
		}
	}
}

double update_eta(int cl)
// updates all eta's and pi's in clause cl 
{
	int i;
	struct clausestruct *c;
	struct literalstruct *l;
	struct pistruct *pi;
	double eps;
	double neweta;
	double allprod=1;
	double wt,wn;
	int zeroes=0;
#ifndef FAST_ITERATION
	double m,p;
#endif
	c=&(clause[cl]);
	for(i=0,l=c->literal; i<c->lits; i++,l++) if(v[l->var].spin==0) {
		pi=&(v[l->var].pi);
#ifdef FAST_ITERATION
		if(l->bar) {
			wt=pi->m;
			wn=pi->p/(1-l->eta)*(1-wt*norho);
		} else {
			wt=pi->p;
			wn=pi->m/(1-l->eta)*(1-wt*norho);
		}
#else
		if(l->bar) {
			m=pi->mzero?0:pi->m;
			if(pi->pzero==0) {
				p=pi->p/(1-l->eta);
			} else if (pi->pzero==1 && 1-l->eta<EPS) {
				p=pi->p;
			} else {
				p=0;
			}
			wn=p*(1-m*norho);
			wt=m;
		} else { 
			p=pi->pzero?0:pi->p;
			if(pi->mzero==0) {
				m=pi->m/(1-l->eta);
			} else if (pi->mzero==1 && 1-l->eta<EPS) {
				m=pi->m;
			} else {
				m=0;
			}
			wn=m*(1-p*norho);
			wt=p;
		}
#endif
		prod[i]=wn/(wn+wt);
		if(prod[i]<EPS) {
			if(++zeroes == 2)
				break;
		} else {
			allprod*=prod[i];
		}
	}
	eps=0;
	for(i=0,l=c->literal; i<c->lits; i++,l++) if(v[l->var].spin==0) {
		if(!zeroes){
			neweta=allprod/prod[i];
		} else if (zeroes==1 && prod[i]<EPS) {
			neweta=allprod;
		} else {
			neweta=0;
		}

		pi=&(v[l->var].pi);
#ifdef FAST_ITERATION
		if(l->bar) {
			pi->p*=(1-neweta)/(1-l->eta);
		} else {
			pi->m*=(1-neweta)/(1-l->eta);
		}
#else			
		if(l->bar) {
			if(1-l->eta>EPS) {
				if(1-neweta>EPS) {
					pi->p*=(1-neweta)/(1-l->eta);
				} else {
					pi->p/=(1-l->eta);
					pi->pzero++;
				} 
			} else {
				if(1-neweta>EPS) {
					pi->p*=(1-neweta);
					pi->pzero--;
				} 
			}
		} else {
			if(1-l->eta>EPS) {
				if(1-neweta>EPS) {
					pi->m*=(1-neweta)/(1-l->eta);
				} else {
					pi->m/=(1-l->eta);
					pi->mzero++;
				} 
			} else {
				if(1-neweta>EPS) {
					pi->m*=(1-neweta);
					pi->mzero--;
				} 
			}
		}
#endif
		if(eps<fabs(l->eta-neweta))
			eps=fabs(fabs(l->eta-neweta));
		l->eta=neweta;
	}
	return eps;
}

struct weightstruct compute_field(int var)
//compute H field of the variable var
{
	struct weightstruct H;
	double p,m;
#ifdef FAST_ITERATION
	p=v[var].pi.p;
	m=v[var].pi.m;
#else
	p=v[var].pi.pzero?0:v[var].pi.p;
	m=v[var].pi.mzero?0:v[var].pi.m;
#endif
	H.z=p*m;
	H.p=m-H.z;
	H.m=p-H.z;
	return normalize(H);
}

void print_fields()
//print all H (non-cavity) fields
{
	int var;
	struct weightstruct H;
	compute_pi();
	for(var=1; var<=N; var++) if(v[var].spin==0) {
		H=compute_field(var);
		fprintf(stderr, "#H(%i)={%f,%f,%f}\n",var,H.p,H.z,H.m);
	}
}

void print_eta()
//print all etas
{
	int c,l;
	for(c=0; c<M; c++)  if(clause[c].type){
		for(l=0;l<clause[c].lits;l++) if(!v[clause[c].literal[l].var].spin){
			fprintf(stderr, "#eta(%i,%i)=%f\n",c,l,clause[c].literal[l].eta);
		}
	}
}

int fix_balanced()
//fix some balanced spin
{
	int var,spin;
	int pap[MAXPAP];
	int npap,totsites=1;
	struct weightstruct H;
	double hphmmin=1000,maxmag=0,summag=0;
	npap=0;
	for(var=1; var<=N && npap<MAXPAP; var++) if(v[var].spin==0) {
		totsites++;
		H=compute_field(var);
		if(fabs(H.p-H.m)<MEBIL && H.z<MEZERO && fabs(H.p-H.m)>MENOBIL) {
			pap[npap++]=var;
			if(fabs(H.p-H.m)<hphmmin) {
				hphmmin=fabs(H.p-H.m);
			}
		}
		maxmag=H.p>H.m?H.p:H.m;
		summag+=maxmag;
	}
	if(npap==0)
		return 0;
	var=pap[randint(npap)];
	H=compute_field(var);
	spin=H.p<H.m?1:-1;
	fprintf(stderr, "fixed balanced\n");
	return !fix(var,spin);
}

int fix_chunk(int quant)
//fix quant spins at a time, taken from list[]
{
	int i;
	struct weightstruct H;
	i=0;
	while (freespin && quant--) {
		while(v[list[i]].spin)
			i++;
		H=compute_field(list[i]);
		if(verbose>2)
			print_stats();
		if(verbose>1)
			fprintf(stderr, "H(%i)={%f,%f,%f} ---> %s\n",list[i],H.p,H.z,H.m,H.p>H.m?"-":"+");
		if(fix(list[i],H.p>H.m?-1:1))
			exit(0);
	}
	return quant;
}

double iterate()
//update etas of clauses in a random permutation order
{
	int cl,vi=0,quant,i;

	double eps,maxeps;
	eps=0;
	maxeps=0;
	for(quant=M-ncl[0];quant;--quant) {
		cl=perm[i=randint(quant)];
		perm[i]=perm[quant-1];
		perm[quant-1]=cl;
		eps=update_eta(cl);
		if(eps>epsilon) {
			vi++;
		}
		if(eps>maxeps) {
			maxeps=eps;
		}
	}
	return maxeps;
}


double compute_sigma()
//compute complexity
{
	int var,cl,i,n;
	double allprod,allprod1,wt,wn;
	double sigmabonds=0, sigmasites=0, sigma=0;
	struct literalstruct *l;
	struct clausestruct *c;
	struct pistruct *pi;
	struct clauselist *cli;
	sigmabonds=0;
	for(cl=0, c=clause; cl<M; c++, cl++) if(c->type) {
		allprod=1;
		allprod1=1;
		for(i=0,l=c->literal; i<c->lits; i++,l++) if(v[l->var].spin==0) {
			pi=&(v[l->var].pi);
#ifdef FAST_ITERATION
			if(l->bar) {
				wn=pi->p/(1-l->eta);
				wt=pi->m;
			} else {
				wn=pi->m/(1-l->eta);
				wt=pi->p;
			}
#else
			if(l->bar) {
				if(1-l->eta>EPS) {
					wn=pi->p/(1-l->eta);
				} else if (pi->pzero==1) {
					wn=pi->p;
				} else {
					wn=0;
				}
				wt=pi->mzero?0:pi->m;
			} else { 
				if(1-l->eta>EPS) {
					wn=pi->m/(1-l->eta);
				} else if (pi->mzero==1) {
					wn=pi->m;
				} else {
					wn=0;
				}
				wt=pi->pzero?0:pi->p;
			}
#endif
			allprod*=wn*(1-wt);
			allprod1*=wt+wn-wt*wn;
		}
		sigmabonds+=log(allprod1-allprod);
	}
	sigmasites=0;
	for(var=1;var<=N;var++) if(v[var].spin==0){
		n=0;
		for(cli=v[var].clauselist,cl=0; cl<v[var].clauses; cli++,cl++) {
			if(cli->clause->type)
				n++;
		}
#ifdef FAST_ITERATION
		wt=v[var].pi.p;
		wn=v[var].pi.m;
#else
		wt=v[var].pi.pzero?0:v[var].pi.p;
		wn=v[var].pi.mzero?0:v[var].pi.m;
#endif
		sigmasites+=log(wt+wn-wt*wn)*(n-1);
	}
	sigma=(sigmabonds-sigmasites)/freespin;
	fprintf(stderr, "bonds=%f sites=%f sigma=%f\n", sigmabonds,sigmasites,sigma);
	return sigma;
}

int sequential_converge()
//call iterate() until the maximum difference of eta with previous 
//step is small.
{
	double eps=0;
	int iter=0,cl,quant;
	compute_pi();
	for(cl=0,quant=0; cl<M; cl++) if(clause[cl].type) {
		perm[quant++]=cl;
	}
	do {
		eps=iterate();
		fprintf(stderr,".");
		fflush(stderr);
	} while (eps>epsilon && iter++<iterations);
	if(eps<=epsilon) {
		fprintf(stderr,":-)\n");
		return 1;
	} else {
		fprintf(stderr,"[%f]:-(\n",eps);
		return 0;
	}
	
}

#ifdef QUEUE

extern int Qlength;


//only neighbors to significatively changed messages are updated
int lazy_converge()
{
	int cl,j,k,steps=0,tot=M,aux,cl2,max=0;
	compute_pi();
//	queue_reset();
//	for(cl=0; cl<M; cl++) if(clause[cl].type) {
//		queue_add(cl);
//		tot++;
//	}
	while((cl=queue_get())!=-1) if(clause[cl].type) {
		if(max<Qlength)
			max=Qlength;
		if(steps++%tot==0) {
			fprintf(stderr, ".");
			fflush(stderr);
		}
		if(steps/tot>iterations) {
			fprintf(stderr, ")^:\n");
			return 0;
		}
		
		if(update_eta(cl)>epsilon) {
			for(j=0; j<clause[cl].lits; j++) { 
				aux=clause[cl].literal[j].var;
				if(!v[aux].spin) {
					for(k=0; k<v[aux].clauses; k++) if(clause[cl2=v[aux].clauselist[k].clause-clause].type) {
						queue_add(cl2);
						
					}
				}
			}
		}
	}
	fprintf(stderr,"(^:\n");
	return 1;
}

#endif //QUEUE

int converge()
{
#ifdef QUEUE
	if(uselazy)
		return lazy_converge();
	else
#endif	//QUEUE	
		return sequential_converge();
}

