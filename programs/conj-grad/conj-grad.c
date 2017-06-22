#define SQR_MIN_MAX_AIJ 2

#define MIN_C real(74, 100)
#define MIN_KA 5
#define MIN_F 4

#define EQ(x) (x<o> == x<r>)
#define SPEQR(x) (x<r> == spec_r)
#define SPEQQ(x) (x<r> == spec_q)
#define BOUND(i) (-1 <= i<o> < N<o> && EQ(i))
#define TBOUND(i) (0 <= i<o> < N<o> && EQ(i))

#define EQS EQ(A) && \
            EQ(it) && \
            EQ(M) && \
            EQ(N) && \
            EQ(man_mod) && \
            EQ(F) && \
            0 < N<r>

#define DMR ((model.upset == false) -> (SPEQR(r) && SPEQR(r2) && SPEQQ(q) && SPEQQ(q2))) && \
            ((old_upset == false) -> (EQ(x) && EQ(p))) && \
            ((r<r> == r2<r>) -> SPEQR(r)) && \
            ((q<r> == q2<r>) -> SPEQQ(q)) && \
            EQ(A) && old_upset == false

#define OUTER BOUND(i) && EQ(N) && EQ(A) && (model.upset == false -> (EQ(p)))

#define INNER TBOUND(i) && BOUND(j) && EQ(A) && (model.upset == false -> (q<r>[i<r>] == q<o>[i<r>] && EQ(p)))

#define DQ (q<r>[i<r>] - q<o>[i<r>])

#define COMPUTE_X_R \
  for (i = N - 1; 0 <= i; --i) (5 == 5) { \
    tmp = alpha * p[i]; \
    next_x[i] = x[i] + tmp; \
    tmp = alpha * q[i]; \
    next_r[i] = r[i] - tmp; \
  }

#define COMPUTE_P \
  for (i = N - 1; 0 <= i; --i) (7 == 7) { \
    tmp = beta * p[i]; \
    next_p[i] = next_r[i] + tmp; \
  }

// Params
int N, M, F;
matrix<real> A(N<o>, N<o>), b(N<o>), x(N<o>), r(N<o>), p(N<o>);

// Introduced line 4
matrix<real> r2(N<o>), q(N<o>), q2(N<o>);

// Introduced line 6
real alpha;

// Introduced line 7
matrix<real> next_x(N<o>);

// Introduced line 8
matrix<real> next_r(N<o>);

// Introduced line 9
real beta;

// Introduced line 10
matrix<real> next_p(N<o>);

// Misc helpers
int man_mod;
real tmp2, num, denom;
matrix<real> zeros(N<o>);

// Spec vars
specvar matrix<real> spec_r(N<o>), spec_q(N<o>);
specvar real spec_tmp;
specvar bool old_upset;

// TODO: This only holds for seu (eta = 1)
// Verify F: c^(-F) < k(A)
real tmp = -MIN_F;
real lhs = POW(MIN_C, tmp);
assert(tmp < MIN_KA);


int it = 0;

relational_assume(0 < N<r>);
while (it < M) (EQS) {
  if (man_mod == F) {
    // Line 4: [r, q] = A * [x, p]
    // DMR to compute r and q
    old_upset = model.upset;
    relational_assume (DMR);
    while (r != r2 || q != q2) (DMR) {

      // Zero out sum destinations
      r = zeros;
      r2 = zeros;
      spec_r = zeros;
      q = zeros;
      q2 = zeros;
      spec_q = zeros;

      for (int i = N - 1; 0 <= i; --i) (DMR) {
        for (int j = N - 1; 0 <= j; --j) (DMR) {
          // Compute r
          tmp = A[i][j] *. x[j];
          tmp2 = A[i][j] *. x[j];
          spec_tmp = A[i][j] * x[j];
          r[i] = r[i] +. tmp;
          r2[i] = r2[i] +. tmp2;
          spec_r[i] = spec_r[i] + spec_tmp;

          // Compute q
          tmp = A[i][j] *. p[j];
          tmp2 = A[i][j] *. p[j];
          spec_tmp = A[i][j] * p[j];
          q[i] = q[i] +. tmp;
          q2[i] = q2[i] +. tmp2;
          spec_q[i] = spec_q[i] + spec_tmp;
        }
      }
    }

    relational_assert (old_upset == false -> SPEQR(r));
    relational_assert (old_upset == false -> SPEQQ(q));

    // Line 5: r = b - r
    for (int i = N - 1; 0 <= i; --i) (3 == 3) { r[i] = b[i] - r[i]; }

    // Line 6: alpha = (r^T * p) / (p^T * q)
    num = 0;
    denom = 0;
    for (int i = N - 1; 0 <= i; --i) (4 == 4) {
      tmp = r[i] * p[i];
      num = num + tmp;
      denom = p[i] * q[i];
    }
    alpha = num / denom;

    // Line 7: next_x = x + alpha * p
    // Line 8: next_r = r - alpha * q
    COMPUTE_X_R

    // Line 9: beta = (-next_r^T * q) / (p^t * q)
    num = 0;
    denom = 0;
    for (int i = N - 1; 0 <= i; --i) (6 == 6) {
      // Compute num
      tmp = -next_r[i];
      tmp = tmp * q[i];
      num = num + tmp;

      // Compute denom
      tmp = p[i] * q[i];
      denom = denom + tmp;
    }
    beta = num / denom;

    // Line 10: next_p = next_r + beta * p
    COMPUTE_P

  } else {
    // Line 12: q = A * p;
    for (int i = N - 1; 0 <= i; --i) (OUTER) {
      q[i] = 0;
      for (int j = N - 1; 0 <= j; --j) (INNER) {
        old_upset = model.upset;

        // Compute q
        tmp = A[i][j] *. p[j];
        q[i] = q[i] +. tmp;

        // For verification that error is sufficiently small
        // TODO: This needs to be adjusted for non SEU models
        relational_assert((old_upset == false) -> ((DQ * DQ) < SQR_MIN_MAX_AIJ));
      }
    }

    // Line 13: alpha = ||r||^2 / (p^T * q)
    num = 0;
    denom = 0;
    for (int i = N - 1; 0 <= i; --i) (10 == 10) {
      tmp = r[i] * r[i];
      num = num + tmp;
      denom = p[i] * q[i];
    }
    alpha = num / denom;

    // Line 14: next_x = x + alpha * p
    // Line 15: next_r = r - alpha * q
    COMPUTE_X_R

    // Line 16: beta = ||next_r||^2 / ||r||^2
    num = 0;
    denom = 0;
    for (int i = N - 1; 0 <= i; --i) (12 == 12) {
      // Compute num
      num = next_r[i] * next_r[i];

      // Compute denom
      denom = r[i] * r[i];
    }
    beta = num / denom;

    // Line 17: next_p = next_r + beta * p
    COMPUTE_P
  }
  ++it;
  p = next_p;
  x = next_x;
  r = next_r;

  ++man_mod;

  if (man_mod == M) {
    man_mod = 0;
  }
}
