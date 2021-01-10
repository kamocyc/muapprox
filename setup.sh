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

sudo mkdir /opt/home2
cd /opt/home2
sudo chown kamo:kamo .dun
mkdir git
cd git
git clone git@github.com:kamocyc/hflmc2.git hflmc2_mora
cd hflmc2_mora

opam install dune.1.11.4 cmdliner.1.0.4 core.v0.13.0 menhir.20190924 ppx_deriving_cmdliner.0.4.1 fmt logs lwt ppx_compare ppx_deriving.4.5 ppx_deriving_cmdliner ppx_let ppx_sexp_conv
dune build -y

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
