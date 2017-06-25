#define E real(1, 1)
#define EPSILON real(10000, 1)

#define XDIST (next_x<o>[upset_index] - next_x<r>[upset_index])

#define EQ(e) (e<o> == e<r>)

#define NZD (forall(fi)((E / EPSILON) < A<r>[fi][fi] || A<r>[fi][fi] < (-(E / EPSILON))))

#define BOUND(i) (-1 <= i<r> < N<r> && EQ(i))
#define TBOUND(i) (0  <= i<r> < N<r> && EQ(i))
#define TBOUNDS(i) (0  <= i < N<r>)

#define SIG ((model.upset == false) -> EQ(sigma)) && \
            ((last_upset == false && model.upset == true) -> (sigma<r> - E < sigma<o> < sigma<r> + E)) && \
            ((last_upset == true && model.upset == true) -> EQ(sigma))

#define UPS ((model.upset == true) -> ((forall(fj)((((i<r>) < fj && fj < N<r>) && (fj != upset_index)) -> next_x<o>[fj] == next_x<r>[fj]))) && \
             -EPSILON < XDIST < EPSILON)

#define OUTER ((model.upset == false) -> (EQ(x) && EQ(next_x))) &&\
              (last_upset == true -> model.upset == true) &&\
              TBOUNDS(upset_index) && NZD && outer_last_upset == model.upset

#define MIDDLE (outer_last_upset == false -> (EQ(x) && (UPS))) &&\
               (last_upset == true-> model.upset == true) &&\
               NZD && TBOUNDS(upset_index) && BOUND(i) &&\
               (model.upset == false -> (outer_last_upset == false && EQ(next_x)))

#define INNER (outer_last_upset == false -> (EQ(x) && (SIG))) &&\
              (last_upset == true -> model.upset == true) &&\
              TBOUND(i) && BOUND(j) &&\
              (model.upset == false -> outer_last_upset == false)

int N, iters;
matrix<real> A(N<r>,N<r>), b(N<r>), x(N<r>), next_x(N<r>);
real sigma, delta, num;
specvar int upset_index = 0;
specvar bool last_upset = false;
specvar bool outer_last_upset = model.upset;
relational_assume (NZD && 0 < N<r>);
while (0 <= iters) (OUTER) {
  for (int i = N - 1; 0 <= i; --i) (MIDDLE) {
    last_upset = model.upset;
    sigma = 0;
    for (int j = N - 1; 0 <= j; --j) (INNER) {
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
