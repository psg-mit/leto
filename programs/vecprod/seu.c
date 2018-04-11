#define EPSILON real(1000, 1)

property_r bounded_diff(matrix<real> x, uint N) :
  forall(uint fi)((fi < N<r>) -> (-EPSILON < x<o>[fi] - x<r>[fi] < EPSILON));

requires forall(uint fi)(0 <= x[fi] < 100 && 0 <= y[fi] < 100)
r_requires eq(N) && eq(x) && eq(y)
matrix<real> product(uint N, matrix<real> x(N), matrix<real> y(N)) {

  matrix<real> result(N);

  @label(loop)
  for (uint i = 0; i < N; ++i)
      (1 == 1)
      (bounded_diff(result, N)) {
    result[i] = x[i] *. y[i];
  }

  relational_assert(bounded_diff(result, N));

  return result;
}
