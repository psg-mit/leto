#define E real(1, 1)
#define EPSILON real(10000, 1)

property nzd(matrix<real> A) :
  forall(fi)((E / EPSILON) < A[fi][fi] || A[fi][fi] < (-(E / EPSILON)));

property_r sig(real sigma, bool last_upset) :
  ((model.upset == false) -> eq(sigma)) &&
  ((last_upset == false && model.upset == true) ->
    (sigma<r> - E < sigma<o> < sigma<r> + E)) &&
  ((last_upset == true && model.upset == true) -> eq(sigma));

property_r bounded_diff_at(matrix<real> x, int index, int i, int N) :
  -EPSILON < x<o>[index] - x<r>[index] < EPSILON &&
  forall(fi)(((i<r> < fi < N<r>) && (fi != index)) -> x<o>[fi] == x<r>[fi]);

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
  specvar bool outer_last_upset = model.upset;
  while (0 <= iters)
        (1 == 1)
        (outer_last_upset == model.upset &&
         0 <= upset_index < N<r> &&
         (outer_last_upset == false -> eq(x)) &&
         ((model.upset == false) -> (eq(next_x)))) {
    for (int i = 0; i < N; ++i)
        (1 == 1)
        (((outer_last_upset == false && model.upset == true) -> bounded_diff_at(next_x, upset_index, i, N)) &&
         (model.upset == false -> (outer_last_upset == false))) {

      specvar bool last_upset = model.upset;
      real sigma = 0;
      @noinf for (int j = 0; j < N; ++j)
          (0 <= i < N && 0 <= j <= N && nzd(A) && 0 < N)
          ((outer_last_upset == false -> sig(sigma, last_upset)) && eq(j) &&
           eq(N) && eq(A) && eq(b) && eq(iters) && eq(i) &&
           (model.upset == false -> (outer_last_upset == false)) &&
           (last_upset == true -> (model.upset == true)) &&
           0 <= upset_index < N<r> &&
           (outer_last_upset == false -> eq(x)) &&
           (model.upset == false -> eq(next_x))) {
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
                        bounded_diff_at(next_x, upset_index, i, N));
    outer_last_upset = model.upset;
  }

  return x;
}
