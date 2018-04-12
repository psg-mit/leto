bool stuck = false;
uint length = 10000;

operator *(x1, x2)
  when (stuck == false || length == 0)
  modifies ()
  ensures (result == x1 * x2);

operator *(x1, x2)
  when (0 < length &&
        ((real(0, 1) <= x1 && real(0,1) <= x2) ||
         (x1 <= real(0, 1) && x2 <= real(0,1))))
  modifies (stuck, length)
  ensures (real(9, 10) * (x1 * x2) <= result <= real(11, 10) * x1 * x2 &&
           stuck == true &&
           length == old(length) - 1);

operator *(x1, x2)
  when (0 < length &&
        ((real(0, 1) <= x1 && x2 <= real(0, 1)) ||
         (x1 <= real(0, 1) && real(0,1) <= x2)))
  modifies (stuck, length)
  ensures (real(11, 10) * (x1 * x2) <= result <= real(9, 10) * x1 * x2 &&
           stuck == true &&
           length == old(length) - 1);
