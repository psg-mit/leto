#define SPEQR(x) x<r> == spec_r
#define SPEQAX(Ax) Ax<r> == spec_Ax

#define OUTER2 ((model.upset == false) -> SPEQR(r)) && \
               ((model.upset == true && old_upset == true) -> SPEQR(r))

#define OLD_UPSET ((init_upset == false) -> (eq(x))) && init_upset == false
#define UPSET2 ((old_upset == false && model.upset == true) -> ((SPEQR(r) && SPEQAX(Ax)) || (SPEQR(r2) && SPEQAX(Ax2)))) && \
               ((model.upset == false) -> (SPEQR(r) && SPEQR(r2) && SPEQAX(Ax) && SPEQAX(Ax2))) && \
               ((model.upset == true && old_upset == true) -> (SPEQR(r) && SPEQR(r2) && SPEQAX(Ax) && SPEQAX(Ax2))) && \
               OLD_UPSET
#define INV eq(N) && eq(A) && eq(b) && UPSET2 && OUTER2

#define IMPL2 ((r<r> == r2<r>) -> SPEQR(r))

#define TRANS (old_upset == true) -> (model.upset == true)

// TODO: Get working with pseudo-seu-range

requires 1 == 1
r_requires eq(N) && eq(A) && eq(b)
matrix<real> correct_sd(int N,
                        matrix<real> A(N, N),
                        matrix<real> b(N),
                        matrix<real> x(N)) {
  matrix<real> Ax(N), r(N), Ax2(N), r2(N);
  real tmp, tmp2;

  // Specvars
  specvar real spec_tmp;
  specvar matrix<real> spec_Ax(N), spec_r(N);
  spec_r = r;

  specvar bool old_upset = false;
  specvar bool init_upset = model.upset;

  // TODO: r == r2 -> (old_upset == model.upset)?  Then I could take this upset
  // thing out of the loop condition
  // TODO: Inference runs out of memory on this loop
  @noinf while (r != r2) (1 == 1) (OUTER2 && IMPL2 && TRANS) {
    old_upset = model.upset;
    relational_assume (INV);
    // TODO: Inference runs out of memory on this loop
    @noinf for (int i = N - 1; 0 <= i; --i) (1 == 1) (INV && TRANS) {
      // recompute Ax[i]
      Ax[i] = 0;
      spec_Ax[i] = 0;
      Ax2[i] = 0;
      // TODO: Inference runs out of memory on this loop
      @noinf for (int j = N - 1; 0 <= j; --j) (1 == 1) (eq(A) && UPSET2 && TRANS) {
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

  relational_assert ((init_upset == false) -> SPEQR(r));

  return r;
}
