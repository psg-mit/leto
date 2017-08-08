#define MIN_ERR 10000

// Reliable
@region(unreliable) fwrite(x1, x2) modifies () ensures (x1 == x2);

// Unreliable
@region(unreliable)
fwrite(x1, x2) modifies () ensures (x2 + MIN_ERR < x1);
