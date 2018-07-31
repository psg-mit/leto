#define MIN_ERR 10000

bool reliable = true;
bool stuck = false;
uint length;

// Reliable
@region(unreliable)
fwrite(x1, x2)
when(reliable == true || length == 0 || stuck == false)
modifies ()
ensures (x1 == x2);

// Unreliable
@region(unreliable)
fwrite(x1, x2)
when (reliable == false && 0 < length)
modifies (stuck, length)
ensures (x2 + MIN_ERR < x1 && stuck == true && length == old(length) - 1);
