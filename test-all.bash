./pp.py models/pseudo-seu-range.c programs/vecprod/seu.c | src/leto
read -p "range seu"

./pp.py models/switchable-rowhammer.c programs/vecprod/rowhammer.c | src/leto
read -p "rowhammer"

./pp.py models/multicycle-add.c programs/vecprod/seu.c | src/leto
read -p "multicycle"

./pp.py models/multicycle-refined.c programs/vecprod/seu.c | src/leto
read -p "refined seu"

./pp.py models/pseudo-seu-range-mult.c programs/jacobi/jacobi-mult-weak.c | src/leto
read -p "Jacobi"

./pp.py models/pseudo-seu-chaos.c programs/sd/sd-freq-errs.c | src/leto
read -p "SD"

./pp.py models/pseudo-seu-range.c programs/conj-grad/conj-grad.c | src/leto
read -p "CG"

./pp.py models/switchable-rowhammer.c programs/cc/switchable-cc.c | src/leto
read -p "rowhammer"
