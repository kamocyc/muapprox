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
#include <setjmp.h>
//#include <malloc.h> //TODO: check if there is no problem even if this line is removed.
#include "random.h"
#include "formula.h"

#ifdef QUEUE

#include "queue.h"

#endif

extern int *ncl;
extern struct clausestruct *clause;
extern struct vstruct *v;
extern int M;
extern int N;
extern int freespin;
extern int verbose;
extern FILE *replay;
extern int maxconn;
extern int maxlit;
extern struct literalstruct *near;
extern int *vic;
extern jmp_buf contradiction;


int fix(int var, int spin)
//fix var to value spin and possibly simplify the resulting formula
{
        freespin--;
	if(v[var].spin)
		return 1;
        v[var].spin=spin;
	if(replay) {
		fprintf(replay, "%i\n",var*spin);
		fflush(replay);
	}

        return simplify(var);
}

void print_stats()
{
	int i;
	for(i=2; i<=maxlit; i++) {
		fprintf(stderr, "\t%i %i-clauses\n", ncl[i], i);
	}
	fprintf(stderr, "\t%i variables\n",freespin);
}

int writesolution(FILE *sink)
//write the solution found so far to a file
{
	int var;
	for(var=1; var<=N; var++){
		if(v[var].spin) {
			fprintf(sink,"%i\n", var*v[var].spin);
		}
	}
	fflush(sink);
	return 0;
}

int writeformula(FILE *sink)
//write formula in dimacs cnf format
{
	int cl,lit,var,bar;
	fprintf(sink, "p cnf %i %i\n", N, M-ncl[0]);
	for(cl=0; cl<M; cl++) if(clause[cl].type) {
		for(lit=0; lit<clause[cl].lits; lit++) {
			var=clause[cl].literal[lit].var;
			bar=clause[cl].literal[lit].bar?-1:1;
			if(v[var].spin==0)
				fprintf(sink, "%i ", var*bar);
		}
		fprintf(sink, "0\n");
	}
	fflush(sink);
	return 0;
}


int writeformulariccardo(FILE *sink)
//write formula in a proprietary format (not used)
{
	int cl,lit;
	fprintf(sink, "%i %i\n", N, M);
	for(cl=0; cl<M; cl++) {
		for(lit=0; lit<3; lit++) {
			fprintf(sink, "%i ", clause[cl].literal[lit].var);
		}
		fprintf(sink, "\n");
		for(lit=0; lit<3; lit++) {
			fprintf(sink, "%i ", clause[cl].literal[lit].bar?-1:1);
		}
		fprintf(sink, "\n");
	}
	fflush(sink);
	return 0;
}

int readvarformula(char *filename)
//read a dimacs cnf formula from a file (not a pipe)
{
	FILE * source;
	struct literalstruct *allliterals=NULL;
	struct clauselist *allclauses;
	int aux,num,cl=0,lit=0,var,literals=0;
	maxconn=0;
        source=fopen(filename,"r");
	if(!source) {
		fprintf(stderr,"error in formula file (unable to read %s)\n",filename);
		exit(-1);
	}
	fprintf(stderr, "reading variable clause-size formula %s ", filename);
//skip comments
	while((aux=getc(source))=='c') {
		while(getc(source)!='\n');
	}
	ungetc(aux,source);
	fprintf(stderr,".");
	fflush(stderr);
//read p line
	fscanf(source, "p cnf %i %i", &N, &M);
	v=calloc(N+1,sizeof(struct vstruct));
	clause=calloc(M,sizeof(struct clausestruct));
//first pass for counting
	fprintf(stderr,".");
	fflush(stderr);
        while(fscanf(source,"%i ",&num)==1) {
		if(!num) {
			if(cl==M) {
				fprintf(stderr,"Too many clauses\n");
				exit(-1);
			}
                        clause[cl].type=lit;
                        clause[cl].lits=lit;
			if(maxlit<lit)
				maxlit=lit;
			lit=0;
			cl++;
                } else {
			var=abs(num);
			if(var>N) {
				fprintf(stderr,"Too many variables\n");
				exit(-1);
			}
			v[var].clauses++;
			if(v[var].clauses>maxconn)
				maxconn=v[var].clauses;
			lit++;
			literals++;
		}
        }
	ncl=calloc(maxlit+1, sizeof(int));
	allliterals=calloc(literals,sizeof(struct literalstruct));
	allclauses=calloc(literals, sizeof(struct clauselist));
	if(!allliterals || !allclauses) {
		fprintf(stderr, "not enough memory!\n");
	}
	for(var=1; var<=N; var++) if(v[var].clauses) {
		v[var].clauselist=allclauses;
		allclauses+=v[var].clauses;
		v[var].clauses=0;
		
	}
	for(cl=0; cl<M; cl++) {
		clause[cl].literal=allliterals;
		allliterals+=clause[cl].lits;
	}
//second pass to do the actual reading
	fprintf(stderr,".");
	fflush(stderr);
	fclose(source);
	source=fopen(filename,"r");
	while((aux=getc(source))=='c') {
		while(getc(source)!='\n');
	}
	ungetc(aux,source);
	fscanf(source, "p cnf %i %i", &N, &M);
	lit=0; 
	cl=0;
        while(fscanf(source,"%i ",&num)==1) {
		if(!num) {
			ncl[lit]++;
			lit=0;
			cl++;
                } else {
			var=abs(num);
			v[var].clauselist[v[var].clauses].clause=clause+cl;
			v[var].clauselist[v[var].clauses++].lit=lit;
			clause[cl].literal[lit].var=var;
			clause[cl].literal[lit].bar=(num<0);
			lit++;
		}
        }
	freespin=N;
	fclose(source);
	fprintf(stderr, "done\nformula read: %i cl, %i vars, %i literals, maxconn=%i, maxliteral=%i c/v=%f\n",M,N,literals,maxconn,maxlit,((double)M)/N);
        return 0;
}





void randomformula(int K)
//random k-sat formula
{
	int used,k,i,j,var,totcl=0;
	struct literalstruct *allliterals;
	struct clauselist *allclauses;
	ncl=calloc(K+1,sizeof(int));
	ncl[K]=M;
	for(i=0; i<K; i++)
		ncl[i]=0;
        clause=calloc(M,sizeof(struct clausestruct));
        v=calloc(N+1,sizeof(struct vstruct));
	allliterals=calloc(K*M,sizeof(struct literalstruct));
	allclauses=calloc(K*M,sizeof(struct clauselist));
	fprintf(stderr, "generating random formula with n=%i m=%i k=%i.",N,M,K);
	fflush(stderr);
	for(i=0; i<M; i++) {
		clause[i].type=K;
		clause[i].lits=K;
		clause[i].literal=allliterals;
		allliterals+=K;
		for(j=0; j<K; j++) {
			do {
				var=randint(N)+1;
				used=0;
				for(k=0;k<j;k++) {
					if(var==clause[i].literal[k].var) {
						used=1;
						break;
					}
				}
			} while (used);
			clause[i].literal[j].var=var;
			clause[i].literal[j].bar=randint(2);
			v[var].clauses++;
			totcl++;
			if(v[var].clauses>maxconn)
				maxconn=v[var].clauses;
		}
	}
	fprintf(stderr, ".");
	fflush(stderr);
	for(var=1; var<=N; var++) if(v[var].clauses){
		v[var].clauselist=allclauses;
		allclauses+=v[var].clauses;
		v[var].clauses=0;
	}
	fprintf(stderr, ".");
	fflush(stderr);
	for(i=0; i<M; i++) {
		for(j=0; j<K; j++) {
			var=clause[i].literal[j].var;
			v[var].clauselist[v[var].clauses].clause=clause+i;
			v[var].clauselist[v[var].clauses++].lit=j;
		}
	}
	maxlit=K;
	freespin=N;
	fprintf(stderr, " done\n");
	fflush(stderr);
}

int simplify(int var)
//simplify after fixing var
{
	int l,aux=0,i;
	struct clausestruct *c;
	int cl;

#ifdef QUEUE
	int var2, j;
#endif
	
	for(cl=0; cl<v[var].clauses; cl++) {
		c=v[var].clauselist[cl].clause;
		l=v[var].clauselist[cl].lit;
		if(c->type==0) {
			continue;
		}
		ncl[c->type]--;
		//check if var renders SAT the clause 
		if(c->literal[l].bar==(v[var].spin==-1)) {
			ncl[0]++;
			c->type=0;
#ifdef QUEUE
			for(i=0; i<c->lits; i++) {
				if(v[var2=c->literal[i].var].spin==0) {
					for(j=0;j<v[var2].clauses; j++)
						queue_add(v[var2].clauselist[j].clause-clause); 
				}
			}
#endif
			continue;
			
		}
		ncl[(--(c->type))]++;
		//otherwise, check for further simplifications
		//type 0, contradiction?:
		if(c->type==0) {
			longjmp(contradiction, 1);
		}
		//no contradiction
		//type 1: unit clause propagation
		if(c->type == 1) {
		//find the unfixed literal
			for(i=0; i<c->lits; i++) {
				if(v[aux=c->literal[i].var].spin==0)
					break;
			}
			if(i==c->lits)
				continue;
                //a clause could be unit-clause-fixed by two different paths  
			if(fix(aux,c->literal[i].bar?-1:1))
				return -1;
		}
#ifdef QUEUE
		queue_add(cl);
#endif
	} 
	return 0;
}

int callwsat(int cutoff, char *formula, char *output)
//call walksat on the remaining formula
{
	char buffer[BUFFERSIZE];
	snprintf(buffer,BUFFERSIZE,"./walksat -seed 1 -solcnf -cutoff %i < %s > %s",cutoff,formula,output);
	printf("calling walksat on the sub-formula (see output in %s)\n",output);
	system(buffer);
	snprintf(buffer,BUFFERSIZE,"grep 'ASSIGNMENT FOUND' %s \n",output);
	if(!system(buffer)) {
		printf("WSAT did find the solution of the sub-formula\n");
		return 1;
	}
	printf("WSAT did NOT find the solution\n");
	printf("Minimum energy reached: ");
	fflush(stdout);
	snprintf(buffer, BUFFERSIZE, "grep -A2 'try.*try.*try' %s|tail -1|cut -c1-10",output);
	system(buffer);
	return 0;
}

int solvesubsystem()
//solve (with walksat) the subsystem and verify
{
	writeformula(fopen(SUBFORMULA,"w+"));
	if(!callwsat(WSATCUTOFF,SUBFORMULA,WSATOUT))
		exit(-1);
	system("cat " WSATOUT "|grep ^v | cut -c3- > " WSATSOL );
	system("./merge " SPSOL " " WSATSOL " > " SOLUTION);
	return !system("./verify " SOLUTION " < " FORMULA);
}
