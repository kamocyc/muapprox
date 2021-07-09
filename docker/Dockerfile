# syntax=docker/dockerfile:1.2

FROM ocaml/opam2:ubuntu-lts as builder
ENV LANG C.UTF-8
ENV ROOT_PATH $HOME/repos

RUN cd $HOME && mkdir repos

RUN sudo apt update && \
    sudo apt install -y build-essential m4 libgmp-dev python2.7 software-properties-common wget

RUN sudo add-apt-repository ppa:avsm/ppa -y && \
    sudo apt update && \
    sudo apt install -y opam

RUN opam init -y && \
    opam update && \
    opam switch create 4.08.1

RUN opam repo set-url default https://opam.ocaml.org && opam update

RUN opam install dune.1.11.4 cmdliner.1.0.4 core.v0.13.0 \
    ppx_deriving_cmdliner.0.4.1 fmt logs lwt ppx_compare ppx_deriving.4.5 \
    ppx_deriving_cmdliner ppx_let ppx_sexp_conv \
    z3.4.8.4 bignum.v0.13.0 async extlib menhir.20190924 -y
    
RUN cd $ROOT_PATH && \
    git clone https://github.com/kamocyc/hflmc2.git hflmc2_mora && \
    cd hflmc2_mora && \
    eval $(opam config env) && \
    dune build
    
# rustup (for hoice)
RUN cd /tmp && \
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh && \
    chmod +x rustup.sh && \
    ./rustup.sh -y
RUN . $HOME/.cargo/env

# Hoice (we need Iwayama version)
RUN cd $ROOT_PATH && \
    git clone https://github.com/Hogeyama/hoice.git && \
    cd hoice && \
    git checkout option-no-inlining && \
    . $HOME/.cargo/env && \
    cargo build --release && \
    sudo cp target/release/hoice /usr/bin/hoice

# z3
RUN cd /tmp && \
    wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip && \
    unzip z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip && \
    sudo cp z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04/bin/z3 /usr/bin/z3

# Java (for Eldarica)
RUN sudo apt install -y default-jre

# Eldarica
RUN cd /tmp && \
    wget https://github.com/uuverifiers/eldarica/releases/download/v2.0.5/eldarica-bin-2.0.5.zip && \
    unzip eldarica-bin-2.0.5.zip && \
    mv eldarica $ROOT_PATH/eldarica && \
    sudo ln -s $ROOT_PATH/eldarica/eld /bin/eld

# for ssh
RUN mkdir -p -m 0700 ~/.ssh && ssh-keyscan github.com >> ~/.ssh/known_hosts && ssh-keyscan bitbucket.org >> ~/.ssh/known_hosts

# Tanahashi solver
# TODO
RUN cd $ROOT_PATHR
# RUN --mount=type=ssh git clone git@github.com:kamocyc/muapprox.git
RUN --mount=type=secret,id=ssh,target=/home/opam/.ssh/id_rsa,uid=1000,gid=1000 ls -la /home/opam/.ssh/id_rsa
# RUN --mount=type=secret,id=ssh,target=/home/opam/.ssh/id_rsa,uid=1000,gid=1000 ssh -vvv git@github.com
RUN --mount=type=secret,id=ssh,target=/home/opam/.ssh/id_rsa,uid=1000,gid=1000 git clone git@github.com:kamocyc/muapprox.git
RUN cd muapprox && \
    eval $(opam config env) && \
    opam install yojson.1.7.0 -y && \
    dune build
    
    
# PCSat (in fptprover repository), which is used by Katsura solver
# Need to enter password
RUN cd $ROOT_PATH
RUN --mount=type=secret,id=ssh,target=/home/opam/.ssh/id_rsa,uid=1000,gid=1000 git clone -b develop --depth 1 git@bitbucket.org:ketanahashi/fptprove.git
RUN cd fptprove && \
    opam switch create latest_dune_4_08_1 4.08.1
RUN sudo apt install -y libblas-dev liblapack-dev pkg-config libffi-dev
RUN eval $(opam config env) && \
    opam install libsvm lp lp-glpk lp-gurobi minisat ocamlgraph ppx_deriving_yojson async core num z3 zarith -y
RUN sudo apt install -y libglpk-dev
RUN eval $(opam config env) && \
    opam switch && \
    opam list
RUN cd $HOME/opam-repository/fptprove && \
    eval $(opam config env) && \
    pwd && \
    dune build main.exe
RUN opam switch 4.08.1

## Set environment variables
RUN echo "export katsura_solver_path=$ROOT_PATH/hflmc2_mora/_build/default/bin/main.exe" >> ~/.profile && \
    echo "export fptprove=/home/opam/opam-repository/fptprove" >>  ~/.profile && \
    . ~/.profile

CMD /home/opam/opam-repository/muapprox/x
