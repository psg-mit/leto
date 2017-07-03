#define MIN_ERR 10000

// Reliable
fread(x1) modifies () ensures (result == x1);

// Unreliable
fread(x1) modifies () ensures (x1 + MIN_ERR < result || result < x1 - MIN_ERR);
