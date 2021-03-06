property_r large_error(matrix<uint> v, uint N) :
  forall(uint fi)(fi < N<r> -> (v<r>[fi] == v<o>[fi] || model.min_error < v<r>[fi]));

requires forall(uint fi)(x[fi] < 100 && y[fi] < 100)
r_requires eq(N) && eq(x) && eq(y)
matrix<uint> product(uint N, matrix<uint> x(N), matrix<uint> y(N)) {
  model.reliable = false;

  @region(unreliable) matrix<uint> result(N);
  @label(loop)
  for (uint i = 0; i < N; ++i)
      (1 == 1)
      (large_error(result, i)) {
    uint prod = x[i] * y[i];
    fwrite(result[i], prod);
  }

  relational_assert(large_error(result, N));

  return result;
}
