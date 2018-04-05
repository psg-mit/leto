bool upset = false;

// Reliable
operator -(x1, x2) modifies () ensures (result == x1 - x2);
operator *(x1, x2) modifies () ensures (result == x1 * x2);
operator /(x1, x2) modifies () ensures (result == x1 / x2);
operator +(x1, x2) modifies () ensures (result == x1 + x2);

// Unreliable
operator /(x1, x2) when (upset == false) modifies (upset) ensures (real(9, 10) <= result / (x1 / x2) <= real(11, 10) && upset == true);
operator -(x1, x2) when (upset == false) modifies (upset) ensures (real(9, 10) <= result / (x1 - x2) <= real(11, 10) && upset == true);
operator +(x1, x2) when (upset == false) modifies (upset) ensures (real(9, 10) <= result / (x1 + x2) <= real(11, 10) && upset == true);
operator *(x1, x2)
  when (upset == false &&
        (((real(0, 1) < x1 && real(0,1) < x2)) ||
         (x1 < real(0, 1) && x2 < real(0,1))))
  modifies (upset)
  ensures (real(9, 10) * (x1 * x2) <= result <= real(11, 10) * x1 * x2 &&
           upset == true);
operator *(x1, x2)
  when (upset == false &&
        ((real(0, 1) < x1 && x2 < real(0, 1)) ||
         (x1 < real(0, 1) && real(0,1) < x2)))
  modifies (upset)
  ensures (real(11, 10) * (x1 * x2) <= result <= real(9, 10) * x1 * x2 &&
           upset == true);
