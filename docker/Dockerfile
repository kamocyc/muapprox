# syntax=docker/dockerfile:1.2

FROM ocaml/opam2:ubuntu-lts as builder
ENV LANG C.UTF-8
ENV ROOT_PATH $HOME/repos

RUN mkdir $HOME/repos

RUN sudo apt update && \
    sudo apt install -y software-properties-common wget build-essential m4 libgmp-dev python2.7 default-jre \
                        libblas-dev liblapack-dev pkg-config libffi-dev libglpk-dev

RUN sudo add-apt-repository ppa:avsm/ppa -y && \
    sudo apt update && \
    sudo apt install -y opam

RUN opam init -y && \
    opam update && \
    opam switch create hflz_solver_4_08_1 4.08.1 && \
    eval $(opam env)

RUN opam repo set-url default https://opam.ocaml.org && opam update

RUN opam install dune.1.11.4 cmdliner.1.0.4 core.v0.13.0 \
    ppx_deriving_cmdliner.0.4.1 fmt logs lwt ppx_compare ppx_deriving.4.5 ppx_let ppx_sexp_conv \
    z3.4.8.4 bignum.v0.13.0 async extlib menhir.20190924 yojson.1.7.0 -y

WORKDIR $ROOT_PATH
RUN git clone https://github.com/kamocyc/hflmc2.git hflmc2_mora
WORKDIR $ROOT_PATH/hflmc2_mora
RUN eval $(opam env) && dune build
    
# rustup (for hoice)
WORKDIR /tmp
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh && \
    chmod +x rustup.sh && \
    ./rustup.sh -y
RUN . $HOME/.cargo/env

# Hoice (we need Iwayama version)
WORKDIR $ROOT_PATH
RUN git clone https://github.com/Hogeyama/hoice.git
WORKDIR $ROOT_PATH/hoice
RUN git checkout option-no-inlining && \
    . $HOME/.cargo/env && \
    cargo build --release && \
    sudo cp target/release/hoice /usr/bin/hoice

# z3 (need the specific z3 version for Hoice to run)
WORKDIR /tmp
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip && \
    unzip z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip && \
    sudo cp z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04/bin/z3 /usr/bin/z3

# Eldarica
WORKDIR /tmp
RUN wget https://github.com/uuverifiers/eldarica/releases/download/v2.0.5/eldarica-bin-2.0.5.zip && \
    unzip eldarica-bin-2.0.5.zip && \
    mv eldarica $ROOT_PATH/eldarica && \
    sudo ln -s $ROOT_PATH/eldarica/eld /bin/eld

# for ssh
RUN mkdir -p -m 0700 ~/.ssh && ssh-keyscan github.com >> ~/.ssh/known_hosts && ssh-keyscan bitbucket.org >> ~/.ssh/known_hosts

# Tanahashi solver
WORKDIR $ROOT_PATH
RUN --mount=type=secret,id=ssh,target=/home/opam/.ssh/id_rsa,uid=1000,gid=1000 git clone git@github.com:kamocyc/muapprox.git
WORKDIR $ROOT_PATH/muapprox
RUN eval $(opam env) && dune build

# PCSat (in fptprover repository), which is used by Katsura solver
# Need to enter password
WORKDIR $ROOT_PATH
RUN --mount=type=secret,id=ssh,target=/home/opam/.ssh/id_rsa,uid=1000,gid=1000 git clone -b develop --depth 1 git@bitbucket.org:ketanahashi/fptprove.git
WORKDIR $ROOT_PATH/fptprove
RUN opam switch create hflz_solver_4_08_1_latest_dune 4.08.1
RUN eval $(opam env) && \
    opam install libsvm lp lp-glpk lp-gurobi minisat ocamlgraph ppx_deriving_yojson async core num z3 zarith -y
RUN eval $(opam env) && \
    dune build main.exe
RUN opam switch hflz_solver_4_08_1 && eval $(opam env)

## TODO: Why this does not work?
WORKDIR $ROOT_PATH/muapprox

# Set environment variables
## TODO: Why this does not work?
RUN echo "export katsura_solver_path=$ROOT_PATH/hflmc2_mora/_build/default/bin/main.exe" >> ~/.profile && \
    echo "export fptprove=$ROOT_PATH/fptprove" >>  ~/.profile && \
    . ~/.profile

CMD $ROOT_PATH/muapprox/x
