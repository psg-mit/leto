#!/usr/bin/env bash

set -e

(
apt-get update
apt-get install -y bisonc++ flexc++ cpp make gcc g++ python python3
) &
(
wget "https://github.com/Z3Prover/z3/archive/z3-4.4.1.tar.gz"
tar xvf z3-4.4.1.tar.gz
) &
wait

cd z3-z3-4.4.1
python scripts/mk_make.py
cd build
make
sudo make install
sudo apt-get install -y clang
cd /vagrant/src
make clean
make
