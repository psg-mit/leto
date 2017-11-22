#define E real(1, 1)
#define EPSILON real(10000, 1)
#define E_REL real(1, 10)


property nzd(matrix<real> A) :
  forall(uint fi)((E / EPSILON) < A[fi][fi] || A[fi][fi] < (-(E / EPSILON)));

property_r sig(real sigma) :
  ((model.upset == false) -> eq(sigma)) &&
  ((old_upset == false && model.upset == true) -> (sigma<r> - E < sigma<o> < sigma<r> + E));


property_r bounded_diff(matrix<real> x) :
  (old_upset == false && model.upset == true) ->
    forall(uint fi)((fi < N<o>) -> (-EPSILON < x<o>[fi] - x<r>[fi] < EPSILON));

requires nzd(A)
r_requires eq(N) && eq(iters) && eq(A) && eq(b) && eq(x)
matrix<real> jacobi(uint N,
                    int iters,
                    matrix<real> A(N,N),
                    matrix<real> b(N),
                    matrix<real> x(N)) {
  @label(out)
  while (0 <= iters)
        (1 == 1)
        (model.upset == false -> eq(x)) {
    specvar bool old_upset = model.upset;
    matrix<real> next_x(N);
    @label(mid)
    for (uint i = 0; i < N; ++i)
        (1 == 1)
        (bounded_diff(next_x) &&
         (model.upset == false -> eq(next_x)) &&
         old_upset == false -> eq(x)) {

      real sigma = 0;
      @label(in)
      for (uint j = 0; j < N; ++j)
          (j <= N)
          ((sig(sigma)) && eq(j)) {
        if (i != j) {
          real delta = A[i][j] *. x[j];
          if (delta <= (-E/E_REL + E) || (E/E_REL - E) <= delta) {
            delta = A[i][j] * x[j];
          }
          sigma = sigma + delta;
        }
      }
      real num = b[i] - sigma;
      next_x[i] = num / A[i][i];
    }
    --iters;
    x = next_x;
    relational_assert(bounded_diff(x));
  }

  return x;
}
