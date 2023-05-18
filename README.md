deprecated in favour of: https://github.com/brando90/ultimate-pycoq

-----
The pip distribution package pycoq provides two python packages:

- serlib

- pycoq


## pycoq

`pycoq` is a python library that provides interface to Coq using the serialization coq-serapi  https://github.com/ejgallego/coq-serapi

## serlib

`serlib` is a python library providing s-expression parser implemented in C++


## Install on Linux

Currently we support only the Linux platform. 

### Build tools
We assume a standard set of building tools. For Ubuntu 20.04 you can get them with
```
apt-get update && apt-get install -y --no-install-recommends ssh git m4 libgmp-dev opam wget ca-certificates rsync strace
```

### External dependencies 

#### opam 
The pycoq calls `opam` package manager to install and run the coq-serapi and coq binaries.
The pycoq assumes that `opam` binary of version 2.* is in the `$PATH`.

On Ubuntu 20.04 install opam with `sudo apt-get install opam`.
See https://opam.ocaml.org/doc/Install.html for other systems. 

#### strace
The pycoq calls `strace` to inspect the building of coq-projects to prepare the context. The pycoq assumes  
that `strace` is in the `$PATH`. 

On Ubuntu 20.04 install strace with `sudo apt-get install strace`.
See https://github.com/strace/strace for other systems.


### Install

Assuming `python>=3.8` and `pip` are in your environment, to install from https://pypi.org/project/pycoq/ run
```
pip install pycoq
```

to install from the github source repository run 
```
pip install git+https://github.com/IBM/pycoq
```

### Test your setup
From your python environment with `pycoq` installed run
```
pytest --pyargs pycoq
```

### Config pycoq
The location of the project directory, debug level and other parameters can be specified in the config file `$HOME/.pycoq`

### Uninstall pycoq 
From your python environment with `pycoq` installed run
```
pip uninstall pycoq
```
By default, pycoq uses directory `$HOME/.local/share/pycoq` to store temporary files such as the opam repository, project files and the logs.
To remove the project directory:
```
rm -fr $HOME/.local/share/pycoq
```
To remove the config file:
```
rm $HOME/.pycoq
```

## Using pycoq
For basics see the example `tutorial/tutorial_pycoq.py` and the test scripts in `pycoq/test`.

## Build pycoq in Docker
Install docker, git clone the source repository and from the directory containing Dockerfile run
```bash
#docker build -f ~/pycoq/Dockerfile_arm -t brandojazz/pycoq:latest_arm ~/pycoq/
docker build -f ~/pycoq/Dockerfile -t brandojazz/pycoq:latest_arm ~/pycoq/
#docker build -t brandojazz/pycoq:latest_arm .

docker login
docker push brandojazz/iit-term-synthesis:test
docker images
```

run container
```bash
#docker pull  brandojazz/iit-term-synthesis:test

docker run --platform linux/amd64 \
            -v /Users/brandomiranda/iit-term-synthesis:/home/bot/iit-term-synthesis \
           -v /Users/brandomiranda/pycoq:/home/bot/pycoq \
           -v /Users/brandomiranda/ultimate-utils:/home/bot/ultimate-utils \
           -v /Users/brandomiranda/proverbot9001:/home/bot/proverbot9001 \
           -v /Users/brandomiranda/data:/home/bot/data \
           -ti brandojazz/iit-term-synthesis:test bash
           
docker run -v /Users/brandomiranda/iit-term-synthesis:/home/bot/iit-term-synthesis \
           -v /Users/brandomiranda/pycoq:/home/bot/pycoq \
           -v /Users/brandomiranda/ultimate-utils:/home/bot/ultimate-utils \
           -v /Users/brandomiranda/proverbot9001:/home/bot/proverbot9001 \
           -v /Users/brandomiranda/data:/home/bot/data \
           -ti brandojazz/iit-term-synthesis:test_arm bash
           
docker run -v /Users/brandomiranda/iit-term-synthesis:/home/bot/iit-term-synthesis \
           -v /Users/brandomiranda/pycoq:/home/bot/pycoq \
           -v /Users/brandomiranda/ultimate-utils:/home/bot/ultimate-utils \
           -v /Users/brandomiranda/proverbot9001:/home/bot/proverbot9001 \
           -v /Users/brandomiranda/data:/home/bot/data \
           -ti ocaml/opam bash
```

## Strace in Apple devices

If you have x86 architeture you might be able to install it on your mac with brew i.e. `brew install strace`:

> Why not install strace externally from your favourite package manager, say brew as in here? You already have root privilege, don't you? This way strace will be called normally in MacOS with full compatibility. 
You might have to do something with your security settings.

ref/credit: https://stackoverflow.com/questions/73724074/how-to-call-an-equivalent-command-to-strace-on-mac-ideally-from-python?noredirect=1#comment130581931_73724074

## Building data sets

TODO

## Current Citation

```
@software{brando2021ultimatepycoq,
    author={Brando Miranda},
    title={Ultimate PyCoq - the Ultimate interface to interact with Coq in Python},
    url={https://github.com/brando90/pycoq},
    year={2022}
}
```
