# HFLz solver

# Installation

The full HFLz solver (by Tanahashi) uses the vHFLz solver (by Katsura) as a backend, which uses Z3, Hoice (the two is for solving CHC), Eldarica (for disproving vHFLz), and PCSat (for solving extended CHC).

**OS: Ubuntu 18.04**

### Create a directory to put repositories

```bash
mkdir ~/repos
cd ~/repos
```

### Install packages

```bash
sudo apt update
sudo apt install build-essential m4 libgmp-dev python2.7 \
                default-jre \
                libblas-dev liblapack-dev pkg-config libffi-dev libglpk-dev

# opam
sudo add-apt-repository ppa:avsm/ppa
sudo apt update
sudo apt install opam

opam init
opam update

# create a new switch, which is used to build solvers
opam switch create hflz_solver_4_08_1 4.08.1
eval $(opam env --switch=hflz_solver_4_08_1)

# need to specify versions
opam install dune.1.11.4 cmdliner.1.0.4 core.v0.13.0 \
    ppx_deriving_cmdliner.0.4.1 fmt logs lwt ppx_compare ppx_deriving.4.5 ppx_let ppx_sexp_conv \
    z3.4.8.4 bignum.v0.13.0 async extlib menhir.20190924 yojson.1.7.0
eval $(opam env)
```

### Build vHFLz solver (developed by Katsura)

```
# (modified version by Tanahashi)
git clone https://github.com/kamocyc/hflmc2.git hflmc2_mora
cd hflmc2_mora
dune build
cd ..
```

### Install Hoice

```
# rustup
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh
chmod +x rustup.sh
./rustup.sh
. $HOME/.cargo/env

# hoice (modified version by Iwayama)
git clone https://github.com/Hogeyama/hoice.git
cd hoice
git checkout option-no-inlining
cargo build --release
sudo cp -i target/release/hoice /usr/bin/hoice
cd ..
```

### Install Z3

We need to install the z3 version 4.8.4 for Hoice to run.

```
wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip
unzip z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip
sudo cp -i z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04/bin/z3 /usr/bin/z3
```

### Install Eldarica

```
wget https://github.com/uuverifiers/eldarica/releases/download/v2.0.5/eldarica-bin-2.0.5.zip
unzip eldarica-bin-2.0.5.zip
sudo ln -s eldarica/eld /bin/eld
```


### Build full HFLz solver (developed by Tanahashi)

```
git clone git@github.com:kamocyc/muapprox.git
cd muapprox
dune build
cd ..
```


### Build PCSat (in fptprover repository), which is used by Katsura solver

```
git clone -b develop --depth 1 git@bitbucket.org:ketanahashi/fptprove.git
cd fptprove

# Create a new switch because PCSat needs a different dune version from one in the Katsura solver in order to be built
opam switch create hflz_solver_4_08_1_latest_dune 4.08.1
eval $(opam env --switch=hflz_solver_4_08_1_latest_dune)

opam install libsvm lp lp-glpk lp-gurobi minisat ocamlgraph ppx_deriving_yojson async core num z3 zarith
eval $(opam env)

dune build main.exe

opam switch hflz_solver_4_08_1
eval $(opam env)
```

### Set environment variables

```
echo "export katsura_solver_path=~/repos/hflmc2_mora/_build/default/bin/main.exe" >> ~/.profile   # This is used by the Tanahashi solver
echo "export fptprove=~/repos/fptprove" >>  ~/.profile  # This is used by the Katsura solver
. ~/.profile
```

### Confirm installation

```
cd ~/repos/muapprox
# In the hflz_solver_4_08_1 switch
./x benchmark/inputs/termination/sum.in                  # valid
./x benchmark/inputs/nontermination/fib_CPS_nonterm.in   # valid
./x benchmark/inputs/termination/notused/sum-invalid.in  # invalid
```

# Usage

## How to run

```
./x FILENAME
# e.g.   ./x benchmark/inputs/termination/sum.in
```

### Output Example

```
[[MAIN]] Verification Result:
  valid
Profiling:
  total: 0.312891 sec
```

(Logs may be output after this. Currently, the solver does not have flags to suppress output)

## Show flags

``./x --help``

## Delete temporary files

``./clean.sh``

## Kill zombie processes

Currently, you need to kill zombie processes if you interrupt the solver with Ctrl+C, or something.

``./killp.sh``
