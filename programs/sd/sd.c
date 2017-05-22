#define EQ(x) x<o> == x<r>
#define SPEQR(x) x<r> == spec_r
#define SPEQAX(Ax) Ax<r> == spec_Ax

#define BOUND(i) (-1 <= i<o> < N<o>)
#define TBOUND(i) (0 <= i<o> < N<o>)

#define OUTER ((model.upset == false) -> EQ(r)) && \
              ((model.upset == true && old_upset == true) -> EQ(r))
#define OUTER2 ((model.upset == false) -> SPEQR(r)) && \
               ((model.upset == true && old_upset == true) -> SPEQR(r))

#define OLD_UPSET ((init_upset == false) -> (EQ(x))) && init_upset == false
#define UPSET ((old_upset == false && model.upset == true) -> ((EQ(r) && EQ(Ax)) || (EQ(r2) && EQ(Ax2)))) && \
              ((model.upset == false) -> (EQ(r) && EQ(r2) && EQ(Ax) && EQ(Ax2))) && \
              ((model.upset == true && old_upset == true) -> (EQ(r) && EQ(r2) && EQ(Ax) && EQ(Ax2))) && \
              OLD_UPSET
#define UPSET2 ((old_upset == false && model.upset == true) -> ((SPEQR(r) && SPEQAX(Ax)) || (SPEQR(r2) && SPEQAX(Ax2)))) && \
               ((model.upset == false) -> (SPEQR(r) && SPEQR(r2) && SPEQAX(Ax) && SPEQAX(Ax2))) && \
               ((model.upset == true && old_upset == true) -> (SPEQR(r) && SPEQR(r2) && SPEQAX(Ax) && SPEQAX(Ax2))) && \
               OLD_UPSET
#define INV EQ(N) && EQ(A) && EQ(b) && UPSET2 && OUTER2

#define IMPL (((r<o> == r2<o>) && (r<r> == r2<r>)) -> EQ(r))
#define IMPL2 ((r<r> == r2<r>) -> SPEQR(r))

// TODO: Get working with pseudo-seu-range

int N;
matrix<real> A(N<o>,N<o>);
matrix<real> b(N<o>);
matrix<real> x(N<o>);

matrix<real> Ax(N<o>);
matrix<real> r(N<o>);
matrix<real> Ax2(N<o>);
matrix<real> r2(N<o>);
real tmp;
real tmp2;

// Specvars
specvar real spec_tmp;
specvar matrix<real> spec_Ax(N<o>);
specvar matrix<real> spec_r(N<o>);

int i;
int j;

specvar bool old_upset;

specvar bool init_upset = model.upset;

relational_assume(OUTER2);
// TODO: r == r2 -> (old_upset == model.upset)?  Then I could take this upset
// thing out of the loop condition
while (r != r2) (OUTER2 && IMPL2) {
  old_upset = model.upset;
  relational_assume (INV);
  for (i = N -. 1; 0 <= i; --.i) (INV) {
    // recompute Ax[i]
    Ax[i] = 0;
    spec_Ax[i] = 0;
    Ax2[i] = 0;
    for (j = N -. 1; 0 <= j; --.j) (EQ(A) && UPSET2) {
      // TODO: Pull assumption into loop inv
      relational_assume ((old_upset == true) -> (model.upset == true));

      tmp = A[i][j] * x[j];
      tmp2 = A[i][j] * x[j];
      spec_tmp = A[i][j] *. x[j];

      Ax[i] = Ax[i] + tmp;
      Ax2[i] = Ax2[i] + tmp2;
      spec_Ax[i] = spec_Ax[i] +. tmp
    };
    // TODO: Pull assumption into loop inv
    relational_assume ((old_upset == true)  -> (model.upset == true));

    r[i] = b[i] -. Ax[i];
    r2[i] = b[i] -. Ax2[i];
    spec_r[i] = b[i] -. spec_Ax[i]
  }
};

//assume (old_upset == model.upset);
relational_assert ((init_upset == false) -> SPEQR(r))
