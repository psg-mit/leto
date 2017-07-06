#define E real(1, 1)
#define EPSILON real(10000, 1)

property nzd(matrix<real> A) :
  forall(fi)((E / EPSILON) < A[fi][fi] || A[fi][fi] < (-(E / EPSILON)));

property_r sig(real sigma, bool last_upset) :
  ((model.upset == false) -> eq(sigma)) &&
  ((last_upset == false && model.upset == true) ->
    (sigma<r> - E < sigma<o> < sigma<r> + E)) &&
  ((last_upset == true && model.upset == true) -> eq(sigma));

property_r bounded_diff_at(matrix<real> x, int index) :
  -EPSILON < x<o>[index] - x<r>[index] < EPSILON;

property_r not_equal_at(matrix<real> v, int i, int N, int index) :
  forall(fi)(((i<r> < fi < N<r>) && (fi != index)) -> v<o>[fi] == v<r>[fi]);

// TODO: Non_relational NZD in requires
requires 0 < N && nzd(A)
r_requires eq(N) && eq(iters) && eq(A) && eq(b) && eq(x)
matrix<real> jacobi(int N,
                    int iters,
                    matrix<real> A(N,N),
                    matrix<real> b(N),
                    matrix<real> x(N)) {
  matrix<real> next_x(N);
  specvar int upset_index = 0;
  specvar bool last_upset = false;
  specvar bool outer_last_upset = model.upset;
  while (0 <= iters)
        (1 == 1)
        ((last_upset == true -> model.upset == true) &&
         0 <= upset_index < N<r> &&
         outer_last_upset == model.upset &&
         ((model.upset == false) -> (eq(x) && eq(next_x)))) {
    // TODO: Try to reduce this again after adding non-relational invariants.
    // BOUND(i) in an unrelational invariant may allow us to infer
    // TBOUNDS(upset_index)
    for (int i = 0; i < N; ++i)
        (0 <= i <= N)
        ((outer_last_upset == false -> (eq(x) &&
                                        (model.upset == true) -> not_equal_at(next_x, i, N, upset_index) &&
                                        bounded_diff_at(next_x, upset_index))) &&
         0 <= upset_index < N<r> &&
         (model.upset == false -> (outer_last_upset == false))) {
      last_upset = model.upset;
      real sigma = 0;
      for (int j = 0; j < N; ++j)
          (0 <= i < N && 0 <= j <= N)
          (outer_last_upset == false -> sig(sigma, last_upset) && eq(j)) {
        if (i != j) {
          real delta = A[i][j] *. x[j];
          sigma = sigma +. delta;
        }
      }
      real num = b[i] - sigma;
      next_x[i] = num / A[i][i];

      if (last_upset == false && model.upset == true) {
        upset_index = i;
      }
    }
    --iters;
    x = next_x;
    relational_assert((outer_last_upset == false && model.upset == true) ->
                        (not_equal_at(next_x, i, N, upset_index) &&
                         bounded_diff_at(next_x, upset_index)));
    outer_last_upset = model.upset;
  }

  return x;
}
