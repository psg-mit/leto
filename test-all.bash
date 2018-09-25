#!/bin/bash

set -e

function run-test {
  echo "----------------------------------------------------------------------"
  echo "Running benchmark: $3"
  echo

  ./pp.py $1 $2 | /usr/bin/time -v src/leto
}

run-test models/pseudo-seu-chaos.c programs/vecprod/seu-dmr.c "Vector product (Figure 3) under SEU (Figure 1)"
run-test models/pseudo-seu-range-mult.c programs/vecprod/seu-mult.c "Vector product (Figure 7) with relative error (Figure 6)"
run-test models/pseudo-seu-range-mult.c programs/jacobi/jacobi-mult-weak.c "Jacobi under multiplicative SEU"
run-test models/pseudo-seu-range.c programs/conj-grad/conj-grad.c "SS-CG under additive SEU"
run-test models/pseudo-seu-chaos.c programs/sd/sd-freq-errs.c "SS-SD under unbounded SEU"
run-test models/pseudo-seu-range.c programs/sd/sd-freq-errs.c "SS-SD under additive SEU"
run-test models/pseudo-seu-range-mult.c programs/sd/sd-freq-errs.c "SS-SD under multiplicative SEU"
run-test models/switchable-rowhammer.c programs/cc/switchable-cc.c "SC-CC under switchable rowhammer"
run-test models/switchable-multicycle-rowhammer.c programs/cc/switchable-cc.c "SC-CC under multicycle"
