# MuHFL

A full-HFLz solver

## Installation

The solver can be built with docker.

```bash
cd docker

# build
DOCKER_BUILDKIT=1 docker build --progress=plain --secret id=ssh,src=<path_to_ssh_private_key> .

# run
docker run -v <path_to_directory_containing_input_files>:/home/opam/inputs/ <image_id> muapprox_main /home/opam/inputs/<input_file_name>

# examples
docker run -v <path_to_repositoy>/benchmark/inputs:/home/opam/inputs/ <image_id> muapprox_main /home/opam/inputs/termination/sum.in                  # valid
docker run -v <path_to_repositoy>/benchmark/inputs:/home/opam/inputs/ <image_id> muapprox_main /home/opam/inputs/nontermination/fib_CPS_nonterm.in   # valid
docker run -v <path_to_repositoy>/benchmark/inputs:/home/opam/inputs/ <image_id> muapprox_main /home/opam/inputs/termination/notused/sum-invalid.in  # invalid
```

## Show help

``docker run <image_id> muapprox_main --help | less``

## Kill zombie processes

Currently, you need to kill zombie processes if you interrupt the solver with Ctrl+C, or something.

``docker run <image_id> killp.sh``
