#define E real(1, 1)
#define EPSILON real(10000, 1)

property nzd(matrix<real> A) :
  forall(uint fi)((E / EPSILON) < A[fi][fi] || A[fi][fi] < (-(E / EPSILON)));

property_r sig(real sigma) :
  ((model.upset == false) -> eq(sigma)) &&
  ((mid[model.upset] == false && model.upset == true) ->
    (sigma<r> - E < sigma<o> < sigma<r> + E)) &&
  ((mid[model.upset] == true && model.upset == true) -> eq(sigma));

property_r bounded_diff_at(matrix<real> x, int index, int i) :
  -EPSILON < x<o>[index] - x<r>[index] < EPSILON &&
  forall(uint fi)((fi < i<r> && fi != index) -> x<o>[fi] == x<r>[fi]);

requires 0 < N && nzd(A)
r_requires eq(N) && eq(iters) && eq(A) && eq(b) && eq(x)
matrix<real> jacobi(int N,
                    int iters,
                    matrix<real> A(N,N),
                    matrix<real> b(N),
                    matrix<real> x(N)) {
  @noinf @label(out)
  while (0 <= iters)
        (0 < N && nzd(A))
        (model.upset == false -> eq(x) &&
         eq(b) && eq(A) && eq(iters) && eq(N)) {
    specvar int upset_index = 0;
    matrix<real> next_x(N);

    @noinf @label(mid)
    for (int i = 0; i < N; ++i)
        (nzd(A))
        (((out[model.upset] == false && model.upset == true) -> bounded_diff_at(next_x, upset_index, i)) &&
         (model.upset == false -> (out[model.upset] == false)) &&
         (model.upset == false) -> eq(next_x) &&
         out[model.upset] == false -> eq(x) &&
         0 <= upset_index < N<r> &&
         eq(A) && eq(b) && eq(N) && eq(iters) && eq(i)) {

      real sigma = 0;
      @noinf @label(in)
      for (int j = 0; j < N; ++j)
          (0 <= i < N && 0 <= j <= N && nzd(A))
          ((out[model.upset] == false -> sig(sigma)) && eq(j) &&
           (mid[model.upset] == true -> (model.upset == true)) &&
           eq(A) && eq(N) && eq(i) &&
           (out[model.upset] == false -> eq(x))) {
        if (i != j) {
          real delta = A[i][j] *. x[j];
          sigma = sigma +. delta;
        }
      }
      real num = b[i] - sigma;
      next_x[i] = num / A[i][i];

      if (mid[model.upset] == false && model.upset == true) {
        upset_index = i;
      }
    }
    --iters;
    x = next_x;
    relational_assert((out[model.upset] == false && model.upset == true) ->
                        bounded_diff_at(next_x, upset_index, i));
  }

  return x;
}
