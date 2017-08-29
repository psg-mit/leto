#define SQR_MIN_MAX_AIJ 2

property_r sqr_lt(matrix<real> v, int i) :
  ((q<r>[i<r>] - q<o>[i<o>]) * (q<r>[i<r>] - q<o>[i<o>])) < SQR_MIN_MAX_AIJ;

property_r dmr_eq(matrix<real> x1, matrix<real> x2, matrix<real> spec_x) :
  x1<r> == spec_x && x2<r> == spec_x;

property_r dmr_imp(matrix<real> x1, matrix<real> x2, matrix<real> spec_x) :
  (x1<r> == x2<r>) -> (x1<r> == spec_x);

requires 0 < N
r_requires eq(N) && eq(M) && eq(F) && eq(A)
matrix<real> ss_cg(int N,
                   int M,
                   int F,
                   matrix<real> A(N, N),
                   matrix<real> b(N),
                   matrix<real> x(N)) {

  // Params
  matrix<real> r(N), p(N);

  // Introduced line 4
  matrix<real> r2(N), q(N), q2(N);

  // Introduced line 6
  real alpha;

  // Introduced line 7
  matrix<real> next_x(N);

  // Introduced line 8
  matrix<real> next_r(N);

  // Introduced line 9
  real beta;

  // Introduced line 10
  matrix<real> next_p(N);

  // Misc helpers
  int man_mod;
  real tmp, tmp2, num, denom;
  matrix<real> zeros(N);

  // Spec vars
  specvar matrix<real> spec_r(N), spec_q(N);
  specvar real spec_tmp;

  int it = 0;

  // Line 1: r = b - Ar (sic.  Should probably be r = b - Ax, which is what
  // we'll do)
  // noinf because we don't actually care about this step for what we're
  // verifying
  @noinf @label(l1)
  for (int i = 0; i < N; ++i) (1 == 1) (1 == 1) {
    tmp = 0;
    @noinf @label(l2)
    for (int j = 0 ; j < N; ++j) (1 == 1) (1 == 1) {
      tmp = tmp + A[i][j] * x[i];
    }
    r[i] = b[i] - tmp;
  }
  p = r;

  // TODO:  Inference on this loop finds nothing because the if branch finding
  // comes back unknown, which causes the system to fall back to weak inference,
  // which comes back unknown in branch finding for all variables one by one.  It
  // takes forever and nothing in learned.
  @noinf @label(outer_while)
  while (it < M)
        (0 < N)
        (eq(A) && eq(it) && eq(M) && eq(N) && eq(man_mod) && eq(F)) {
    if (man_mod == F) {
      // Line 4: [r, q] = A * [x, p]
      // DMR to compute r and q
      r2 = r;
      spec_r = r;
      q2 = q;
      spec_q = q;
      bool not_run = true;
      @noinf @label(outer_dmr)
      while (not_run == true || r != r2 || q != q2)
            (2 == 2)
            (((model.upset == false) -> (dmr_eq(r, r2, spec_r) &&
                                        dmr_eq(q, q2, spec_q))) &&
             dmr_imp(r, r2, spec_r) &&
             dmr_imp(q, q2, spec_q)) {
        not_run = false;

        // TODO: Inference runs out of memory.
        @label(middle_dmr)
        for (int i = N - 1; 0 <= i; --i)
            (2 == 2)
            (2 == 2) {

          @label(inner_dmr) for (int j = N - 1; 0 <= j; --j) (1 == 1) (1 == 1) {
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

      relational_assert (outer_while[model.upset] == false -> (r<r> == spec_r));
      relational_assert (outer_while[model.upset] == false -> (q<r> == spec_q));

      // Line 5: r = b - r
      @noinf @label(l5)
      for (int i = N - 1; 0 <= i; --i) (1 == 1) (3 == 3) { r[i] = b[i] - r[i]; }

      // Line 6: alpha = (r^T * p) / (p^T * q)
      num = 0;
      denom = 0;
      @noinf @label(l6) for (int i = N - 1; 0 <= i; --i) (1 == 1) (4 == 4) {
        tmp = r[i] * p[i];
        num = num + tmp;
        denom = p[i] * q[i];
      }
      alpha = num / denom;

      // Line 7: next_x = x + alpha * p
      // Line 8: next_r = r - alpha * q
      @noinf @label(xra) for (i = 0; i  < N; ++i) (5 == 5) (5 == 5) {
        tmp = alpha * p[i];
        next_x[i] = x[i] + tmp;
        tmp = alpha * q[i];
        next_r[i] = r[i] - tmp;
      }

      // Line 9: beta = (-next_r^T * q) / (p^t * q)
      num = 0;
      denom = 0;
      @noinf @label(l9) for (int i = N - 1; 0 <= i; --i) (1 == 1) (6 == 6) {
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
      @noinf @label(pa) for (i = 0; i < N; ++i) (7 == 7) (7 == 7) {
        tmp = beta * p[i];
        next_p[i] = next_r[i] + tmp;
      }
    } else {
      // Line 12: q = A * p;
      @label(outer_err)
      for (int i = N - 1; 0 <= i; --i) (-1 <= i < N) (eq(i)) {
        q[i] = 0;
        @label(inner_err)
        for (int j = N - 1; 0 <= j; --j)
            (-1 <= j < N && 0 <= i < N)
            ((model.upset == false && eq(p)) -> q<r>[i<r>] == q<o>[i<o>]) {
          // Compute q
          tmp = A[i][j] *. p[j];
          q[i] = q[i] +. tmp;

          // For verification that error is sufficiently small
          // TODO: This needs to be adjusted for non SEU models
          relational_assert((inner_err[model.upset] == false && eq(p)) -> sqr_lt(q, i));
        }
      }

      // Line 13: alpha = ||r||^2 / (p^T * q)
      num = 0;
      denom = 0;
      @noinf @label(l13)
      for (int i = N - 1; 0 <= i; --i) (10 == 10) (10 == 10) {
        tmp = r[i] * r[i];
        num = num + tmp;
        denom = p[i] * q[i];
      }
      alpha = num / denom;

      // Line 14: next_x = x + alpha * p
      // Line 15: next_r = r - alpha * q
      @noinf @label(xrb) for (i = 0; i  < N; ++i) (5 == 5) (5 == 5) {
        tmp = alpha * p[i];
        next_x[i] = x[i] + tmp;
        tmp = alpha * q[i];
        next_r[i] = r[i] - tmp;
      }

      // Line 16: beta = ||next_r||^2 / ||r||^2
      num = 0;
      denom = 0;
      @noinf @label(l16)
      for (int i = N - 1; 0 <= i; --i) (12 == 12) (12 == 12) {
        // Compute num
        num = next_r[i] * next_r[i];

        // Compute denom
        denom = r[i] * r[i];
      }
      beta = num / denom;

      // Line 17: next_p = next_r + beta * p
      @noinf @label(pb) for (i = 0; i < N; ++i) (7 == 7) (7 == 7) {
        tmp = beta * p[i];
        next_p[i] = next_r[i] + tmp;
      }
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
  return x;
}
