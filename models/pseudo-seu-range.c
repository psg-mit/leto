bool upset;
upset = false;

// Reliable
operator -(x1, x2) when (true) modifies (nil) ensures (result == x1 - x2);
operator *(x1, x2) when (true) modifies (nil) ensures (result == x1 * x2);
operator /(x1, x2) when (true) modifies (nil) ensures (result == x1 / x2);
operator +(x1, x2) when (true) modifies (nil) ensures (result == x1 + x2);
fread(x1) when (true) modifies (nil) ensures (result == x1);

// Unreliable
operator /(x1, x2) when (upset == false) modifies (upset, nil) ensures (result < x1 / x2 + 1 && x1 / x2 - 1 < result && upset == true);
operator -(x1, x2) when (upset == false) modifies (upset, nil) ensures (result < x1 - x2 + 1 && x1 - x2 - 1 < result && upset == true);
operator +(x1, x2) when (upset == false) modifies (upset, nil) ensures (result < x1 + x2 + 1 && x1 + x2 - 1 < result && upset == true);
operator *(x1, x2) when (upset == false) modifies (upset, nil) ensures (result < x1 * x2 + 1 && x1 * x2 - 1 < result && upset == true);
fread(x1) when (upset == false) modifies (upset, nil) ensures (result < x1 + 1 && x1 - 1 < result && upset == true)
