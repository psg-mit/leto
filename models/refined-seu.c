#include "pseudo-seu-chaos.c"

// Unreliable
@refines(1)
operator *(x1, x2)
  when (upset == false &&
        ((real(0, 1) < x1 && real(0,1) < x2) ||
         (x1 < real(0, 1) && x2 < real(0,1))))
  modifies (upset)
  ensures (real(9, 10) * (x1 * x2) <= result <= real(11, 10) * x1 * x2 &&
           upset == true);
@refines(1)
operator *(x1, x2)
  when (upset == false &&
        ((real(0, 1) < x1 && x2 < real(0, 1)) ||
         (x1 < real(0, 1) && real(0,1) < x2)))
  modifies (upset)
  ensures (real(11, 10) * (x1 * x2) <= result <= real(9, 10) * x1 * x2 &&
           upset == true);

@refines(1)
  operator +(x1, x2)
  when (upset == false &&
        ((real(0, 1) < x1 && real(0,1) < x2) ||
         (x1 < real(0, 1) && x2 < real(0,1))))
  modifies (upset)
  ensures (real(9, 10) * (x1 + x2) <= result <= real(11, 10) * (x1 + x2) &&
           upset == true);
@refines(1)
operator +(x1, x2)
  when (upset == false &&
        ((real(0, 1) < x1 && x2 < real(0, 1)) ||
         (x1 < real(0, 1) && real(0,1) < x2)))
  modifies (upset)
  ensures (real(11, 10) * (x1 + x2) <= result <= real(9, 10) * (x1 + x2) &&
           upset == true);

@refines(1)
    operator -(x1, x2)
  when (upset == false &&
        ((real(0, 1) < x1 && real(0,1) < x2) ||
         (x1 < real(0, 1) && x2 < real(0,1))))
  modifies (upset)
  ensures (real(9, 10) * (x1 - x2) <= result <= real(11, 10) * (x1 - x2) &&
           upset == true);
@refines(1)
operator -(x1, x2)
  when (upset == false &&
        ((real(0, 1) < x1 && x2 < real(0, 1)) ||
         (x1 < real(0, 1) && real(0,1) < x2)))
  modifies (upset)
  ensures (real(11, 10) * (x1 - x2) <= result <= real(9, 10) * (x1 - x2) &&
           upset == true);

@refines(1)
  operator /(x1, x2)
  when (upset == false &&
        ((real(0, 1) < x1 && real(0,1) < x2) ||
         (x1 < real(0, 1) && x2 < real(0,1))))
  modifies (upset)
  ensures (real(9, 10) * (x1 / x2) <= result <= real(11, 10) * (x1 / x2) &&
           upset == true);
@refines(1)
operator /(x1, x2)
  when (upset == false &&
        ((real(0, 1) < x1 && x2 < real(0, 1)) ||
         (x1 < real(0, 1) && real(0,1) < x2)))
  modifies (upset)
  ensures (real(11, 10) * (x1 / x2) <= result <= real(9, 10) * (x1 / x2) &&
           upset == true);
