#!/bin/bash

## ここから実行したコマンド

sudo apt update
sudo apt install -y build-essential m4 libgmp-dev python2.7

sudo add-apt-repository ppa:avsm/ppa  -y
sudo apt update
sudo apt install -y opam

opam init -y
opam switch create 4.08.1

# GitHubにSSH鍵を登録
# FPTProverの権限

sudo mkdir /opt/home2
cd /opt/home2
sudo chown kamo:kamo .dun
mkdir git
cd git
git clone git@github.com:kamocyc/hflmc2.git hflmc2_mora
cd hflmc2_mora

opam install dune.1.11.4 cmdliner.1.0.4 core.v0.13.0 menhir.20190924 ppx_deriving_cmdliner.0.4.1 fmt logs lwt ppx_compare ppx_deriving.4.5 ppx_deriving_cmdliner ppx_let ppx_sexp_conv
dune build

cd ..
git clone git@github.com:kamocyc/muapprox.git
cd muapprox

opam install z3.4.8.4 bignum.v0.13.0 async extlib -y

# rustup
cd /tmp
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh
chmod +x rustup.sh
./rustup.sh -y
source $HOME/.cargo/env

# hoice
cd /opt/home2/git
git clone git@github.com:Hogeyama/hoice.git
cd hoice
git checkout option-no-inlining
cargo build --release
sudo cp target/release/hoice /usr/bin/hoice

# z3
cd /tmp
wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip
unzip z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip
sudo cp z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04/bin/z3 /usr/bin/z3

# Eldarica
cd /tmp
wget https://github.com/uuverifiers/eldarica/releases/download/v2.0.5/eldarica-bin-2.0.5.zip
unzip eldarica-bin-2.0.5.zip
mv eldarica ~/eldarica
sudo ln -s ~/eldarica/eld /bin/eld

# Java (for Eldarica)
sudo apt install -y default-jre

# OCamlPlatform
# OCamlLSP needs latest opam packages. So, we need a seperate switch.
opam switch create latest_dune_4_08_1 ocaml-base-compiler.4.08.1
opam install ocaml-lsp-server -y
opam switch 4.08.1


# fptprover
cd /opt/home2/git
# ! パスワード入力が必要
git clone -b develop --depth 1 git@bitbucket.org:ketanahashi/fptprove.git
cd fptprove
opam switch latest_dune_4_08_1
sudo apt install -y libblas-dev liblapack-dev pkg-config libffi-dev
opam install libsvm lp lp-glpk lp-gurobi minisat ocamlgraph ppx_deriving_yojson -y
eval $(opam env)
opam install async core num z3 zarith -y
dune build
opam switch 4.08.1
echo "export fptprove=/opt/home2/git/fptprove" >>  ~/.profile
. ~/.profile

# docker
sudo apt-get remove docker docker-engine docker.io containerd runc
sudo apt-get install -y \
    apt-transport-https \
    ca-certificates \
    curl \
    gnupg-agent \
    # software-properties-common
curl -fsSL https://download.docker.com/linux/ubuntu/gpg | sudo apt-key add -
sudo apt-key fingerprint 0EBFCD88
sudo add-apt-repository \
   "deb [arch=amd64] https://download.docker.com/linux/ubuntu \
   $(lsb_release -cs) \
   stable"
sudo apt-get update
sudo apt-get install -y docker-ce docker-ce-cli containerd.io
sudo service docker start


# SAS19 (koba-test)
cd /opt/home2/git
git clone -b koba-test --depth 1 https://kamocyc@bitbucket.org/ketanahashi/fptprove.git fptprove_muarith
cd fptprove_muarith
dune build

# Iwayama solver

sudo apt install apt-utils pkg-config autoconf libmpfr-dev libgmp-dev libglpk-dev m4 libipc-system-simple-perl libstring-shellquote-perl -y

mkdir $HOME/depend

opam switch create 4.06.1
opam install camlp4 camlp5 extlib batteries zarith apron.20160125 glpk.0.1.8 z3.4.7.1 -y

eval $(opam env)

# このイメージだとglpkのインストールエラーは出ないようだ。
# opam install glpk.0.1.8 ; exit 0

# ppx_deriving_cmdliner のバージョンの指定が必要（指定しないと0.4.0が入り、cmdlinerが無効のようなエラーになる）
opam install cmdliner core fmt logs lwt menhir ppx_compare ppx_deriving ppx_deriving_cmdliner.0.4.1 ppx_let ppx_sexp_conv spawn re2 -y

# fpat
######

git clone https://github.com/hopv/MoCHi $HOME/depend/mochi-for-fpat
cd $HOME/depend/mochi-for-fpat/csisat
git checkout 688c094876c8fe121a50f1a1de55eb5e1d3a3e5f
opam exec -- make lib
cd $HOME/depend/mochi-for-fpat/fpat
eval `opam config env` && \
    autoconf && \
    ./configure && \
    make install-lib && \
    make depend && \
    make && \
    make install

################################################################################
# Build & Install
################################################################################

git clone https://github.com/Hogeyama/hflmc2 $HOME/hflmc2
cd $HOME/hflmc2
git pull 
        # このコミットは存在しない
        # && git checkout 8b98ff694fa451f13edac3daa01acc78b1f3eb8b
eval `opam config env` && \
    dune build && \
    dune install && \
    sudo cp `which hflmc2` /bin
sudo cp .circleci/horsat2 /bin
sudo chmod 755 /bin/horsat2

sudo cp $HOME/.opam/4.06.1/share/apron/lib/lib* /usr/lib/x86_64-linux-gnu/
sudo cp $HOME/.opam/4.06.1/lib/z3/lib* /usr/lib/x86_64-linux-gnu/

################################################################################
# FOO
################################################################################

# FROM ubuntu:16.04
# COPY --from=builder /home/opam/.opam/4.06/share/apron/lib/lib* /usr/lib/x86_64-linux-gnu/
# COPY --from=builder /home/opam/.opam/4.06/lib/z3/lib* /usr/lib/x86_64-linux-gnu/
# COPY --from=builder /usr/lib/x86_64-linux-gnu/libglpk.* /usr/lib/x86_64-linux-gnu/
# COPY --from=builder /usr/lib/x86_64-linux-gnu/libmpfr.* /usr/lib/x86_64-linux-gnu/
# COPY --from=builder /usr/lib/x86_64-linux-gnu/libgmp.* /usr/lib/x86_64-linux-gnu/
# COPY --from=builder /usr/lib/x86_64-linux-gnu/libamd.* /usr/lib/x86_64-linux-gnu/
# COPY --from=builder /usr/lib/x86_64-linux-gnu/libcolamd.* /usr/lib/x86_64-linux-gnu/
# COPY --from=builder /usr/lib/x86_64-linux-gnu/libltdl.* /usr/lib/x86_64-linux-gnu/
# COPY --from=builder /usr/lib/x86_64-linux-gnu/libgomp.* /usr/lib/x86_64-linux-gnu/
# COPY --from=builder /usr/lib/x86_64-linux-gnu/libsuitesparseconfig.* /usr/lib/x86_64-linux-gnu/
# COPY --from=builder /bin/ /bin/