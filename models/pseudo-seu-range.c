bool upset = false;

// Reliable
operator -(x1, x2) modifies () ensures (result == x1 - x2);
operator *(x1, x2) modifies () ensures (result == x1 * x2);
operator /(x1, x2) modifies () ensures (result == x1 / x2);
operator +(x1, x2) modifies () ensures (result == x1 + x2);
fread(x1) modifies () ensures (result == x1);

// Unreliable
operator /(x1, x2) when (upset == false) modifies (upset) ensures (x1 / x2 - 1 < result < x1 / x2 + 1 && upset == true);
operator -(x1, x2) when (upset == false) modifies (upset) ensures (x1 - x2 - 1 < result < x1 - x2 + 1 && upset == true);
operator +(x1, x2) when (upset == false) modifies (upset) ensures (x1 + x2 - 1 < result < x1 + x2 + 1 && upset == true);
operator *(x1, x2) when (upset == false) modifies (upset) ensures (x1 * x2 - 1 < result < x1 * x2 + 1 && upset == true);
fread(x1) when (upset == false) modifies (upset) ensures (x1 - 1 < result < x1 + 1 && upset == true)
