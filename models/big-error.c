#define MIN_ERR 10000

// Reliable
@region(unreliable) fwrite(x1, x2) modifies () ensures (x1 == x2);
@region(unreliable) fread(x1) modifies () ensures (x1 == result);

// Unreliable
@region(unreliable)
fwrite(x1, x2) modifies () ensures (x2 + MIN_ERR < x1 ||  x1 < x2 - MIN_ERR);
@region(unreliable)
fread(x1) modifies () ensures (x1 + MIN_ERR < result || result < x1 - MIN_ERR);
