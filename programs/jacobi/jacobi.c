#define E real(2, 1)
#define EPSILON real(10000, 1)

#define XDIST (next_x<o>[upset_index] - next_x<r>[upset_index])

#define EQ(e) (e<o> == e<r>)

#define NZD (forall(fi)((E / EPSILON) < A<r>[fi][fi] || A<r>[fi][fi] < (real(0, 1) - (E / EPSILON))))

#define BOUND(i) ((0 - 2) < i<r> && i<r> < N<r> && EQ(i))
#define TBOUND(i) (0  <= i<r> && i<r> < N<r> && EQ(i))
#define TBOUNDS(i) (0  <= i && i < N<r>)

#define SIG ((model.upset == false) -> EQ(sigma)) && \
            ((last_upset == false && model.upset == true) -> ((sigma<r> < sigma<o> + E) && sigma<o> - E < sigma<r>)) && \
            ((last_upset == true && model.upset == true) -> EQ(sigma))

#define UPS ((model.upset == false) -> (forall(fi)((((i<r>) < fi && fi < N<r>)) -> next_x<o>[fi] == next_x<r>[fi]))) && \
            ((model.upset == true) -> ((forall(fj)((((i<r>) < fj && fj < N<r>) && (fj != upset_index)) -> next_x<o>[fj] == next_x<r>[fj]))) && \
             (real(0, 1) - EPSILON) < XDIST &&  XDIST < EPSILON)

#define OUTER ((model.upset == false) -> (EQ(x) && EQ(next_x))) &&\
              (last_upset == true -> model.upset == true) &&\
              EQ(iters) && EQ(N)  && EQ(A) && EQ(b) && TBOUNDS(upset_index) && NZD &&\
              outer_last_upset == model.upset

#define MIDDLE (outer_last_upset == false -> (EQ(x) && (UPS))) &&\
               (last_upset == true-> model.upset == true) &&\
               NZD && EQ(N) && TBOUNDS(upset_index) && EQ(A) && BOUND(i) && EQ(b) &&\
               (model.upset == false -> outer_last_upset == false)

#define INNER (outer_last_upset == false -> (EQ(x) && (SIG))) &&\
              (last_upset == true -> model.upset == true) &&\
              EQ(A) && TBOUND(i) && BOUND(j) &&\
              (model.upset == false -> outer_last_upset == false)

int N;
matrix<real> A(N<r>,N<r>);
matrix<real> b(N<r>);
real sigma;
real delta;
real num;
int i;
int j;
int iters;
specvar int upset_index;
specvar bool last_upset;
specvar bool outer_last_upset;
matrix<real> x(N<r>);
matrix<real> next_x(N<r>);
relational_assume (OUTER);
while (0 <= iters) (OUTER) {
  for (i = N -. 1; 0 <= i; --.i) (MIDDLE) {
    last_upset = model.upset;
    sigma = real(0, 1);
    for (j = N -. 1; 0 <= j; --.j) (INNER) {
      delta = real(0, 1);
      if (i != j) {
        delta = A[i][j] * x[j];
        sigma = sigma + delta
      }
    };
    num = b[i] -. sigma;
    next_x[i] = num /. A[i][i];

    if (last_upset == false && model.upset == true) {
      upset_index = i
    }
  };
  --.iters;
  COPY(next_x, x);
  relational_assert(outer_last_upset == false -> (UPS));
  outer_last_upset = model.upset
}
