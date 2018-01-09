// params
int N;
matrix<real> A(N, N);
matrix<real> b(N);
matrix<real> x(N);

// TODO: Init r
matrix<real> r(N);

// TODO: Loop
specvar matrix<real> old_x(N);


bool converged = false;
@noinf @label(outer)
while (converged == false)
      (1 == 1)
      (eq(converged) &&
       eq(A) &&
       eq(x) &&
       eq(r)) {
  old_x = x;

  // TODO: Regions

  // Matrix vector product
  matrix<real> q(N);
  @noinf @label(outer_q)
  for (int i = 0; i < N; ++i)
      (1 == 1)
      (eq(q) &&
       eq(A) &&
       eq(x) &&
       eq(i) &&
       eq(N)) {
    q[i] = 0;
    @noinf @label(inner_q)
    for (int j = 0; j < N; ++j)
        (0 < j <= N)
        (eq(q) &&
         eq(A) &&
         eq(x) &&
         eq(i) &&
         eq(j) &&
         eq(N)) {
      real delta = A[i][j] * x[j];
      q[i] = q[i] + delta;
    }
  }

  // Compute ||r||^2 and rtq
  real r_sq_norm = 0;
  real rtq = 0;
  @noinf @label(r_related)
  for (int i = 0; i < N; ++i)
      (0 < i <= N)
      (eq(r_sq_norm) &&
       eq(rtq) &&
       eq(r) &&
       eq(i) &&
       eq(N) &&
       eq(q)) {
    real delta = r[i] * r[i];
    r_sq_norm = r_sq_norm + delta;
    delta = r[i] * q[i];
    rtq = rtq + delta;
  }

  // Compute updates
  real alpha = r_sq_norm / rtq;
  matrix<real> next_x(N);
  matrix<real> next_r(N);
  @noinf @label(update)
  for (int i = 0; i < N; ++i)
      (4 == 4)
      (eq(next_x) &&
       eq(next_r) &&
       eq(q) &&
       eq(alpha) &&
       eq(r) &&
       eq(i) &&
       eq(x) &&
       eq(N)) {
    real prod = alpha * r[i];
    next_x[i] = x[i] + prod;
    prod = alpha * q[i];
    next_r[i] = r[i] - prod;
  }

  // TODO: begin commit
  x = next_x;
  // TODO: end commit

  //relational_assert(x<r> == old_x || eq(x));

  r = next_r;

  // TODO: Convergence check
}
