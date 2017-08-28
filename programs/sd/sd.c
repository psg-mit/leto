#define SPEQR(x) x<r> == spec_r
#define SPEQAX(Ax) Ax<r> == spec_Ax

#define OUTER2 ((model.upset == false) -> SPEQR(r)) && \
               ((model.upset == true && outer[model.upset] == true) -> SPEQR(r))

#define UPSET2 ((outer[model.upset] == false && model.upset == true) -> ((SPEQR(r) && SPEQAX(Ax)) || (SPEQR(r2) && SPEQAX(Ax2)))) && \
               ((model.upset == false) -> (SPEQR(r) && SPEQR(r2) && SPEQAX(Ax) && SPEQAX(Ax2))) && \
               ((model.upset == true && outer[model.upset] == true) -> (SPEQR(r) && SPEQR(r2) && SPEQAX(Ax) && SPEQAX(Ax2)))
#define INV UPSET2 && OUTER2

#define IMPL2 ((r<r> == r2<r>) -> SPEQR(r))

property_r trans(bool b) : (outer[model.upset] == true) -> (model.upset == true);

property_r upset2(int x) : UPSET2;

property_r outer2(int x) : OUTER2;


// TODO: Get working with pseudo-seu-range

requires 1 == 1
r_requires model.upset == false
matrix<real> correct_sd(int N,
                        matrix<real> A(N, N),
                        matrix<real> b(N),
                        matrix<real> x(N)) {
  matrix<real> zeros(N);

  matrix<real> Ax(N), r(N), Ax2(N), r2(N);
  real tmp, tmp2;

  // Specvars
  specvar real spec_tmp;
  specvar matrix<real> spec_Ax(N), spec_r(N);
  spec_r = r;

  // TODO: r == r2 -> (old_upset == model.upset)?  Then I could take this upset
  // thing out of the loop condition
  // TODO: Inference runs out of memory on this loop
  @noinf @label(outer)
  while (r != r2) (1 == 1) (outer2(r) && IMPL2 && trans(r)) {
    Ax = zeros;
    Ax2 = zeros;
    spec_Ax = zeros;
    r = zeros;
    r2 = zeros;
    spec_r = zeros;

    // TODO: Inference runs out of memory on this loop
    @noinf @label(middle)
    for (int i = N - 1; 0 <= i; --i)
        (1 == 1)
        (upset2(i) && outer2(r) && trans(r)) {
      // recompute Ax[i]
      Ax[i] = 0;
      spec_Ax[i] = 0;
      Ax2[i] = 0;
      // TODO: Inference runs out of memory on this loop
      @noinf @label(inner)
      for (int j = N - 1; 0 <= j; --j)
          (1 == 1)
          (upset2(i) && trans(r)) {
        tmp = A[i][j] *. x[j];
        tmp2 = A[i][j] *. x[j];
        spec_tmp = A[i][j] * x[j];

        Ax[i] = Ax[i] +. tmp;
        Ax2[i] = Ax2[i] +. tmp2;
        spec_Ax[i] = spec_Ax[i] + tmp;
      }

      r[i] = b[i] - Ax[i];
      r2[i] = b[i] - Ax2[i];
      spec_r[i] = b[i] - spec_Ax[i];
    }
  }

  relational_assert (SPEQR(r));

  return r;
}
