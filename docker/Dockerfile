# syntax = docker/dockerfile:experimental

FROM ocaml/opam:ubuntu-20.04-ocaml-4.12 as builder
ENV LANG C.UTF-8
ENV ROOT_PATH $HOME/repos

RUN mkdir $HOME/repos

RUN sudo apt update && sudo apt install wget -y
RUN eval $(opam env) && opam install dune cmdliner core fmt logs lwt menhirLib ppx_compare \
  ppx_deriving ppx_deriving_cmdliner ppx_let ppx_sexp_conv menhir async yojson -y

# katsura-solver
WORKDIR $ROOT_PATH
RUN git clone https://github.com/kamocyc/hflmc2.git hflmc2_mora
WORKDIR $ROOT_PATH/hflmc2_mora
RUN eval $(opam env) && dune build bin/main.exe

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
RUN --mount=type=secret,id=ssh,target=/home/opam/.ssh/id_rsa,uid=1000,gid=1000 ls /home/opam/.ssh/id_rsa
RUN --mount=type=secret,id=ssh,target=/home/opam/.ssh/id_rsa,uid=1000,gid=1000 git clone git@github.com:kamocyc/muapprox.git
WORKDIR $ROOT_PATH/muapprox
RUN git checkout develop
RUN eval $(opam env) && dune build bin/muapprox_main.exe

# PCSat (in fptprover repository), which is used by Katsura solver
WORKDIR $ROOT_PATH
RUN --mount=type=secret,id=ssh,target=/home/opam/.ssh/id_rsa,uid=1000,gid=1000 git clone -b develop --depth 1 git@bitbucket.org:ketanahashi/fptprove.git
WORKDIR $ROOT_PATH/fptprove
RUN sudo apt install libblas-dev libgmp-dev liblapack-dev pkg-config python2.7 libffi-dev libglpk-dev libmpfr-dev -y
RUN eval $(opam env) && opam install oUnit ocamlgraph ppx_deriving_yojson z3 zarith libsvm lp lp-glpk lp-gurobi minisat apronext -y
RUN eval $(opam env) && dune build main.exe


ENV katsura_solver_path=$ROOT_PATH/hflmc2_mora/_build/default/bin/main.exe \
    fptprove=$ROOT_PATH/fptprove

ENV CMD_PATH /usr/bin/muapprox_main
RUN sudo touch $CMD_PATH && \
    sudo chown opam:opam $CMD_PATH && \
    echo "#!/bin/bash" > $CMD_PATH && \
    echo "cd $ROOT_PATH/muapprox" >> $CMD_PATH && \
    echo "_build/default/bin/muapprox_main.exe \$@" >> $CMD_PATH && \
    chmod +x $CMD_PATH

WORKDIR $ROOT_PATH

CMD ["muapprox_main"]
