bool upset = false;

// Reliable
operator -(x1, x2) when (true) modifies (nil) ensures (result == x1 - x2);
operator *(x1, x2) when (true) modifies (nil) ensures (result == x1 * x2);
operator /(x1, x2) when (true) modifies (nil) ensures (result == x1 / x2);
operator +(x1, x2) when (true) modifies (nil) ensures (result == x1 + x2);

// Unreliable
operator /(x1, x2) when (upset == false) modifies (upset, nil) ensures (result == x1 / x2 + 1 && upset == true);
operator -(x1, x2) when (upset == false) modifies (upset, nil) ensures (result == x1 - x2 + 1 && upset == true);
operator +(x1, x2) when (upset == false) modifies (upset, nil) ensures (result == x1 + x2 + 1 && upset == true);
operator *(x1, x2) when (upset == false) modifies (upset, nil) ensures (result == x1 * x2 + 1 && upset == true)
