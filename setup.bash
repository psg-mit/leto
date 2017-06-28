#!/usr/bin/env bash

set -e

(
apt-get update
apt-get install -y bisonc++ flexc++ cpp make gcc g++ python python3 ntp
) &
(
wget "https://github.com/Z3Prover/z3/archive/z3-4.5.0.tar.gz"
tar xvf z3-4.5.0.tar.gz
) &
wait

cd z3-z3-4.5.0
python scripts/mk_make.py
cd build
make
make install
apt-get install -y clang
cd /vagrant/src
make clean
make
