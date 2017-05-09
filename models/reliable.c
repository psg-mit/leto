bool upset;
upset = false;
operator -(x1, x2) when (true) modifies (nil) ensures (result == x1 - x2);
operator *(x1, x2) when (true) modifies (nil) ensures (result == x1 * x2);
operator /(x1, x2) when (true) modifies (nil) ensures (result == x1 / x2);
operator +(x1, x2) when (true) modifies (nil) ensures (result == x1 + x2);
fread(x1) when (true) modifies (nil) ensures (result == x1)
