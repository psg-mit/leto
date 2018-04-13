#define MIN_ERR 10000

property_r large_error(matrix<real> v, uint N) :
  forall(uint fi)(fi < N<r> -> (v<r>[fi] == v<o>[fi] || MIN_ERR < v<r>[fi]));

requires forall(uint fi)(0 <= x[fi] < 100 && 0 <= y[fi] < 100)
r_requires eq(N) && eq(x) && eq(y)
matrix<real> product(uint N, matrix<real> x(N), matrix<real> y(N)) {
  model.reliable = false;

  @region(unreliable) matrix<real> result(N);
  @label(loop)
  for (uint i = 0; i < N; ++i)
      (1 == 1)
      (large_error(result, N)) {
    real prod = x[i] * y[i];
    fwrite(result[i], prod);
  }

  relational_assert(large_error(result, N));

  return result;
}
