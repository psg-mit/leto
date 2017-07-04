#define MAX_N 10000

#define EQ_TO(X, index) (forall(fi)((0 <= fi < index) -> (X<o>[fi] == X<r>[fi])))

#define INV forall(fi)(next_CC<r>[fi] == nextCC<o>[fi] || v<r> < next_CC<r>[v<r>] || next_CC<r>[v<r>] < 0)

#define SPEC_FROM(from, to, X, spec_X) forall(fi)((from <= fi < to) -> X[fi] == spec_X[fi])

property mat_bound(matrix<real> A, real max) :
  forall(fi)(forall(fj)(0 <= A[fi][fj] < max));

property vec_bound(matrix<real> V, int to, int max) :
  forall(fi)((0 <= fi < to) -> (0 <= V[fi] < max));


// Inputs
// TODO: I'm assuming that the vertices are numbered 0 to N (exclusive).
// Thus, there is no V vector in this implementation
requires N < MAX_N && mat_bound(adj, N)
r_requires eq(N) && eq(adj)
matrix<int> cc(int N, matrix<int> adj(N, N+1)) {
  // Helpers
  int i;
  int j;
  int v;
  int u;
  int N_s;
  matrix<int> CC(N);
  matrix<int> next_CC(N);
  matrix<int> P_star(N);
  specvar matrix<int> spec_next_CC(N);

  // Line 1: for each v in V do
  // TODO: Prove CCBOUND over this loop, remove from OUTER assumption
  for (v = 0; v < N; ++v) (vec_bound(CC, v, N)) (1 == 1) {
    // Line 2: CC^1[v] = v;
    //         CC^0[v] = v;
    //         P*[v] = -1;
    next_CC[v] = v;
    CC[v] = v;
    P_star[v] = -1;
  }

  // Line 3: i = 1;
  i = 1;

  // Line 4: N_s = |V|
  N_s = N;

  // Line 5: while N_s > 0 do:
  // TODO: Enable inference (across the whole file)
  @noinf while (0 < N_s) (N < MAX_N && mat_bound(adj, N)) (eq(N)) {
    // Line 6: MemCpy(CC^i, CC^{i-1}, |V|)
    next_CC = CC;
    spec_next_CC = CC;

    // Line 7: for each v in V do
    for (v = 0; v < N; ++v) (0 <= v <= N) (1 == 1) {
      // Line 8: for each u in adj(v) do:
      for (j = 0; j < adj[v][N]; ++j) (0 <= j <= N && 0 <= v < N) (1 == 1) {

        u = adj[v][j];

        // Line 9: if CC^{i-1}[u] < CC^{i-1}[v] then
        if (CC[u] < CC[v]) {
          // TODO: Put next_CC and P_star in unreliable memory so that bad
          // writes cause errors.  CC should non be in unreliable memory
          // because it could cause a bad branch which would violate the
          // property we care about.
          //
          // Alternatively, repeatly read CC[u] and CC[v] until we get valid
          // values (easy) and use those values for our branch

          // Line 10: CC^i[v] = CC^{i-1}[u]
          next_CC[v] = fread(CC[u]);
          spec_next_CC[v] = CC[u];

          // Line 11: P*[v] = &u
          P_star[v] = fread(j);

          assert(vec_bound(CC, N, N) -> (next_CC[v] == spec_next_CC[v] ||
                                         v < next_CC[v] ||
                                         next_CC[v] < 0));
        }
      }
    }

    // Fault detection and correction (reliable)
    // Line 12: N_s = 0
    N_s = 0;

    // Line 13: for each v in V do
    for (v = 0; v < N; ++v) (0 <= v <= N) (1 == 1) {
      // Line 14: if Eq 1 (Section 5) does not hold for v then
      // TODO:  flip this conditional and remove else branch
      if (0 <= next_CC[v] <= v &&
          -1 <= P_star[v] <= adj[v][N] &&
          ((next_CC[v] == v && P_star[v] == -1) ||
           (next_CC[v] == CC[adj[v][P_star[v]]] && P_star[v] != -1))) {
        skip;
      } else {

        // Line 15: CC^i[v] = CC^{i-1}[v]
        next_CC[v] = CC[v];
        spec_next_CC[v] = CC[v];

        // Line 16: for each u in adj(v) do
        @noinf for (j = 0; j < adj[v][N]; ++j) (0 <= v < N && mat_bound(adj, N) && next_CC[v] == spec_next_CC[v]) (1 == 1) {
          u = adj[v][j];

          //  Line 17: if CC^{i-1}[u] < CC^i[v] then
          if (CC[u] < next_CC[v]) {
            // Line 18: CC^i[v] = CC^{i-1}[u]
            next_CC[v] = CC[u];
            spec_next_CC[v] = CC[u];

            // Line 19: P*[v] = &u
            P_star[v] = j;

            // CCBOUND restored for next iteration
            assert(vec_bound(CC, N, N) -> (0 <= next_CC[v] < N));
          }
        }
      }

      // Line 20: if CC^i[v] != CC^{i-1}[v] then
      if (next_CC[v] != CC[v]) {
        // Line 21: N_s = N_s + 1
        ++N_s;
      }
    }

    // Line 22: i = i + 1
    ++i;

    // Update CC
    CC = next_CC;
  }


  return CC;
}
