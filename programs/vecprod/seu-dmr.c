property_r eq_array(matrix<real> x, uint N):
  forall(uint fi)((fi < N<r>) -> (x<o>[fi] == x<r>[fi]));

requires 1 == 1
r_requires eq(N) && eq(x) && eq(y)
matrix<real> product(uint N, matrix<real> x(N), matrix<real> y(N)) {

  matrix<real> result(N);

  @label(loop)
  for (uint i = 0; i < N; ++i)
      (1 == 1)
      (eq_array(result, i)) {
    real d_1 = x[i] *. y[i];
    real d_2 = x[i] *. y[i];

    if (d_1 != d_2) {
      d_1 = x[i] *. y[i];
    }

    result[i] = d_1;

  }

  relational_assert(eq_array(result, N));

  return result;
}
