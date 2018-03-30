#define MIN_ERR 10000

bool reliable = true;

// Reliable
@region(unreliable) fwrite(x1, x2) modifies () ensures (x1 == x2);

// Unreliable
@region(unreliable)
fwrite(x1, x2)
when (reliable == false)
modifies ()
ensures (x2 + MIN_ERR < x1);
