requires 1 == 1
r_requires 1 == 1
real avg(int N, matrix<real> x(N)) {
  real sum = 0;
  @label(loopy)
    // TODO: sum<o> is within 10% of sum<r>
  for (int i = 0; i < N; ++i) (1 == 1) (1 == 1) {
    sum = sum + x[i];
  }

  /* TODO: This doesn't work because of mixing reals and ints in division */
  //real avg = sum / N;

  return avg;
}
