#!/bin/bash

set -e

function run-test {
  echo "----------------------------------------------------------------------"
  echo "Running benchmark: $3"
  echo

  ./pp.py $1 $2 | /usr/bin/time -v src/leto
}

run-test models/pseudo-seu-range.c programs/vecprod/seu.c "Vector product (Figure 4) under addtive SEU (Figure 3)"
run-test models/switchable-rowhammer.c programs/vecprod/rowhammer.c "Vector product (Figure 6) under switchable rowhammer (Figure 5)"
run-test models/multicycle-add.c programs/vecprod/seu.c "Vector product (Figure 4) under multicycle (Figure 7)"
run-test models/multicycle-refined.c programs/vecprod/seu.c "Vector product (Figure 4) under refined SEU (Figure 8)"
run-test models/pseudo-seu-range-mult.c programs/jacobi/jacobi-mult-weak.c "Jacobi (Figure 14) under multiplicative SEU (Figure 13)"
run-test models/pseudo-seu-range.c programs/conj-grad/conj-grad.c "SS-CG (Appendix H) under additive SEU (Figure 3)"
run-test models/pseudo-seu-chaos.c programs/sd/sd-freq-errs.c "SS-SD (Figure 31) under unbounded SEU (Figure 1)"
run-test models/switchable-rowhammer.c programs/cc/switchable-cc.c "SC-CC (Figure 27) under switchable rowhammer (Figure 5)"
