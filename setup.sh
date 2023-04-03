#!/usr/bin/env bash
mkdir -p lfind
cd lfind

git clone git@github.com:yalhessi/lemmafinder.git
pushd lemmafinder
git checkout develop
popd

opam switch create 4.07.1+flambda
opam repo add coq-released https://coq.inria.fr/opam/released
opam install dune=2.7.1 core=v0.12.4 menhir=20200624 coq=8.11.2 coq-serapi=8.11.0+0.11.0 coq-mathcomp-ssreflect=1.11.0 coq-quickchick=1.3.2 parmap=1.2.3 base-bigarray

python3 -m venv lfindenv
source lfindenv/bin/activate
pip3 install matplotlib tabulate

git clone https://github.com/UCSD-PL/proverbot9001.git
pushd proverbot9001
git submodule init coq_serapy
git submodule init dataloader/gestalt-ratio
git submodule update
pip3 install --no-input -r requirements.txt
pip3 install --no-input -e coq_serapy
rustup toolchain install nightly
(cd dataloader/dataloader-core && maturin develop -r)
make download-weights
popd

git clone git@github.com:qsctr/coq-synth.git
pushd coq-synth
opam install . --deps-only
dune build && dune install
popd

git clone git@github.com:QuickChick/QuickChick.git
pushd QuickChick
git checkout v1.3.2
cp ../lemmafinder/patch/quickChick.mlg src/.
make && make install
popd

echo "export PROVERBOT=$PWD/proverbot9001" >> lfindenv/bin/activate
echo "export LFIND=$PWD/lemmafinder" >> lfindenv/bin/activate
source lfindenv/bin/activate

pushd lemmafinder
opam config subst theories/LFindLoad.v
dune build && dune build && dune install
popd 
echo "Done building LFind."