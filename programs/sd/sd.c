property_r trans(bool nil) : (outer[model.upset] == true) -> (model.upset == true);

property_r upset2(matrix<real> r, matrix<real> r2, matrix<real> spec_r,
                  matrix<real> Ax, matrix<real> Ax2, matrix<real> spec_Ax) :
  ((outer[model.upset] == false && model.upset == true) ->
    ((r<r> == spec_r && Ax<r> == spec_Ax) || (r2<r> == spec_r && Ax2<r> == spec_Ax))) &&
  ((model.upset == false || outer[model.upset] == true) ->
    (r<r> == spec_r && r2<r> == spec_r && Ax<r> == spec_Ax && Ax2<r> == spec_Ax));

property_r outer(matrix<real> r, matrix<real> spec_r) :
  ((model.upset == false || outer[model.upset] == true) -> r<r> == spec_r);


// TODO: Get working with pseudo-seu-range

requires 1 == 1
r_requires 1 == 1
matrix<real> correct_sd(int N,
                        matrix<real> A(N, N),
                        matrix<real> b(N),
                        matrix<real> x(N)) {
  matrix<real> zeros(N);
  @noinf @label(zero_init) for (int i = 0; i < N; ++i) (1 == 1) (1 == 1) {
    zeros[i] = 0;
  }

  matrix<real> r(N), r2(N);

  // Specvars
  specvar matrix<real> spec_r(N);
  spec_r = r;

  bool run = false;

  // TODO: Inference runs out of memory on this loop
  @noinf @label(outer)
  while (run == false || r != r2)
        (1 == 1)
        (outer(r, spec_r) && ((r<r> == r2<r>) -> r<r> == spec_r) && trans(r)) {
    run = true;

    matrix<real> Ax(N), Ax2(N);
    specvar matrix<real> spec_Ax(N);

    Ax = zeros;
    Ax2 = zeros;
    spec_Ax = zeros;
    r = zeros;
    r2 = zeros;
    spec_r = zeros;

    // TODO: Inference runs out of memory on this loop
    @noinf @label(middle)
    for (int i = 0; i < N; ++i)
        (1 == 1)
        (upset2(r, r2, spec_r, Ax, Ax2, spec_Ax) && outer(r, spec_r) && trans(r)) {
      // recompute Ax[i]
      // TODO: Inference runs out of memory on this loop
      @noinf @label(inner)
      for (int j = 0; j < N; ++j)
          (1 == 1)
          (upset2(r, r2, spec_r, Ax, Ax2, spec_Ax) && trans(r)) {
        real tmp = A[i][j] *. x[j];
        real tmp2 = A[i][j] *. x[j];
        specvar real spec_tmp = A[i][j] * x[j];

        Ax[i] = Ax[i] +. tmp;
        Ax2[i] = Ax2[i] +. tmp2;
        spec_Ax[i] = spec_Ax[i] + tmp;
      }

      r[i] = b[i] - Ax[i];
      r2[i] = b[i] - Ax2[i];
      spec_r[i] = b[i] - spec_Ax[i];
    }
  }

  relational_assert (r<r> == spec_r);

  return r;
}
