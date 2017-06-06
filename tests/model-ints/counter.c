int ops = 0;

operator -(x1, x2) modifies (ops) ensures (result == x1 - x2 && ops == old(ops) + 1);
operator *(x1, x2) modifies (ops) ensures (result == x1 * x2 && ops == old(ops) + 1);
operator /(x1, x2) modifies (ops) ensures (result == x1 / x2 && ops == old(ops) + 1);
operator +(x1, x2) modifies (ops) ensures (result == x1 + x2 && ops == old(ops) + 1);
fread(x1) modifies (ops) ensures (result == x1 && ops == old(ops) + 1);
