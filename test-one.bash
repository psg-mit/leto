#!/bin/bash

set -e

echo "Running benchmark"
echo

./pp.py $1 $2 | /usr/bin/time -v src/leto
