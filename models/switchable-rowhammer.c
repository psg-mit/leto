uint min_error = 10;
bool reliable = true;

// Reliable
@region(unreliable) fwrite(x1, x2) modifies () ensures (x1 == x2);

// Unreliable
@region(unreliable)
fwrite(x1, x2)
when (reliable == false)
modifies ()
ensures (min_error < x1);
