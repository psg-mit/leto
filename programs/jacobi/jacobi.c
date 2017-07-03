#define E real(1, 1)
#define EPSILON real(10000, 1)

#define XDIST (next_x<o>[upset_index] - next_x<r>[upset_index])

#define NZD (forall(fi)((E / EPSILON) < A[fi][fi] || A[fi][fi] < (-(E / EPSILON))))

#define BOUND(i) (-1 <= i < N)
#define TBOUND(i) (0  <= i < N)
#define TBOUNDS(i) (0  <= i < N<r>)

#define SIG ((model.upset == false) -> eq(sigma)) && \
            ((last_upset == false && model.upset == true) -> (sigma<r> - E < sigma<o> < sigma<r> + E)) && \
            ((last_upset == true && model.upset == true) -> eq(sigma))

#define UPS ((model.upset == true) -> ((forall(fj)((((i<r>) < fj && fj < N<r>) && (fj != upset_index)) -> next_x<o>[fj] == next_x<r>[fj]))) && \
             -EPSILON < XDIST < EPSILON)

#define OUTER ((model.upset == false) -> (eq(x) && eq(next_x))) &&\
              (last_upset == true -> model.upset == true) &&\
              TBOUNDS(upset_index) && outer_last_upset == model.upset

#define MIDDLE (outer_last_upset == false -> (eq(x) && (UPS))) &&\
               TBOUNDS(upset_index) &&\
               (model.upset == false -> (outer_last_upset == false && eq(next_x)))

#define INNER (outer_last_upset == false -> (SIG))

// TODO: Non_relational NZD in requires
requires 0 < N && NZD
r_requires eq(N) && eq(iters) && eq(A) && eq(b) && eq(x)
matrix<real> jacobi(int N,
                    int iters,
                    matrix<real> A(N,N),
                    matrix<real> b(N),
                    matrix<real> x(N)) {
  matrix<real> next_x(N);
  real sigma, delta, num;
  specvar int upset_index = 0;
  specvar bool last_upset = false;
  specvar bool outer_last_upset = model.upset;
  while (0 <= iters) (1 == 1) (OUTER) {
    // TODO: Try to reduce this again after adding non-relational invariants.
    // BOUND(i) in an unrelational invariant may allow us to infer
    // TBOUNDS(upset_index)
    for (int i = N - 1; 0 <= i; --i) (BOUND(i)) (MIDDLE) {
      last_upset = model.upset;
      sigma = 0;
      for (int j = N - 1; 0 <= j; --j) (TBOUND(i) && BOUND(j)) (INNER) {
        delta = 0;
        if (i != j) {
          delta = A[i][j] *. x[j];
          sigma = sigma +. delta;
        }
      }
      num = b[i] - sigma;
      next_x[i] = num / A[i][i];

      if (last_upset == false && model.upset == true) {
        upset_index = i;
      }
    }
    --iters;
    x = next_x;
    relational_assert(outer_last_upset == false -> (UPS));
    outer_last_upset = model.upset;
  }

  return x;
}
