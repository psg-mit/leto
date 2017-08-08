bool upset = false;

operator -(x1, x2) modifies () ensures (result == x1 - x2);
operator *(x1, x2) modifies () ensures (result == x1 * x2);
operator /(x1, x2) modifies () ensures (result == x1 / x2);
operator +(x1, x2) modifies () ensures (result == x1 + x2);

@region(unreliable) fwrite(x1, x2) modifies () ensures (x1 == x2);
@region(unreliable) fread(x1) modifies () ensures (result == x1);
