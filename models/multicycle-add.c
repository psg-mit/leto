#define ERROR 1

bool stuck = false;
uint length;

@refines(9999)
operator *(x1, x2)
  when (stuck == false || length == 0)
  modifies ()
  ensures (result == x1 * x2);

@refines(9999)
operator *(x1, x2)
  when (0 < length)
  modifies (stuck, length)
  ensures (stuck == true &&
           length == old(length) - 1 &&
           x1 * x2 - ERROR < result < x1 * x2 + ERROR);
