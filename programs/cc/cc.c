#define MAX_N 10000

property mat_bound(matrix<real> A, int max) :
  forall(fi)(forall(fj)(0 <= A[fi][fj] < max));

property vec_bound(matrix<real> V, int to, int max) :
  forall(fi)((0 <= fi < to) -> (0 <= V[fi] < max));

property large_error(matrix<real> x, matrix<real> spec_x, int v) :
  x[v] == spec_x[v] || v < x[v] || x[v] < 0;

requires N < MAX_N && mat_bound(adj, N)
r_requires 1 == 1
matrix<int> cc(int N, matrix<int> adj(N, N+1)) {
  // Helpers
  matrix<int> CC(N);
  @region(unreliable) matrix<int> next_CC(N);
  matrix<int> corrected_next_CC(N);
  matrix<int> P_star(N);
  specvar matrix<int> spec_next_CC(N);

  // Line 1: for each v in V do
  for (int v = 0; v < N; ++v) (vec_bound(CC, v, N)) (1 == 1) {
    // Line 2: CC^1[v] = v;
    //         CC^0[v] = v;
    //         P*[v] = -1;
    next_CC[v] = v;
    CC[v] = v;
    P_star[v] = -1;
  }

  // Line 3: i = 1;
  int i = 1;

  // Line 4: N_s = |V|
  int N_s = N;

  // Line 5: while N_s > 0 do:
  while (0 < N_s) (1 == 1) (1 == 1) {
  //@noinf while (0 < N_s) (N < MAX_N && mat_bound(adj, N)) (eq(N)) {
    // Line 6: MemCpy(CC^i, CC^{i-1}, |V|)
    for (int v = 0; v < N; ++v) (0 <= v <= N) (1 == 1) {
      next_CC[v] = CC[v];
      spec_next_CC[v] = CC[v];

      assert(vec_bound(CC, N, N) -> large_error(next_CC, spec_next_CC, v));
    }

    // Line 7: for each v in V do
    for (int v = 0; v < N; ++v) (0 <= v <= N) (1 == 1) {
      // Line 8: for each u in adj(v) do:
      for (int j = 0; j < adj[v][N]; ++j) (0 <= j <= N && 0 <= v < N) (1 == 1) {

        int u = adj[v][j];

        // Line 9: if CC^{i-1}[u] < CC^{i}[v] then
        if (CC[u] < next_CC[v]) {
          // Line 10: CC^i[v] = CC^{i-1}[u]
          next_CC[v] = CC[u];
          spec_next_CC[v] = CC[u];

          // Line 11: P*[v] = &u
          P_star[v] = j;

          assert(vec_bound(CC, N, N) -> large_error(next_CC, spec_next_CC, v));
        }
      }
    }

    // Fault detection and correction (reliable)

    // Set corrected_next_CC to be full of -1 (an invalid result)
    @noinf for (int v = 0; v < N; ++v) (1 == 1) (1 == 1) {
      corrected_next_CC[v] = -1;
    }


    // Line 12: N_s = 0
    N_s = 0;

    // Line 13: for each v in V do
    for (int v = 0; v < N; ++v) (0 <= v <= N) (1 == 1) {
      // Line 14: if Eq 1 (Section 5) does not hold for v then
      // TODO:  flip this conditional and remove else branch
      if (0 <= next_CC[v] <= v &&
          -1 <= P_star[v] <= adj[v][N] &&
          ((next_CC[v] == v && P_star[v] == -1) ||
           (next_CC[v] == CC[adj[v][P_star[v]]] && P_star[v] != -1))) {
        skip;
      } else {

        // Line 15: CC^i[v] = CC^{i-1}[v]
        corrected_next_CC[v] = CC[v];
        spec_next_CC[v] = CC[v];

        // Line 16: for each u in adj(v) do
        @noinf for (int j = 0; j < adj[v][N]; ++j)
                   (0 <= v < N &&
                    mat_bound(adj, N) &&
                    corrected_next_CC[v] == spec_next_CC[v])
                   (1 == 1) {
          int u = adj[v][j];

          //  Line 17: if CC^{i-1}[u] < CC^i[v] then
          if (CC[u] < next_CC[v]) {
            // Line 18: CC^i[v] = CC^{i-1}[u]
            corrected_next_CC[v] = CC[u];
            spec_next_CC[v] = CC[u];

            // Line 19: P*[v] = &u
            P_star[v] = j;

            // CCBOUND restored for next iteration
            assert(vec_bound(CC, N, N) -> (0 <= corrected_next_CC[v] < N));
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

    // Update CC (merge results)
    for (int v = 0; v < N; ++v) (1 == 1) (1 == 1) {
      if (corrected_next_CC[v] == -1) {
        CC[v] = next_CC[v];
        assert(CC[v] == next_CC[v]);
      } else {
        CC[v] = corrected_next_CC[v];
        assert(CC[v] == corrected_next_CC[v]);
      }
    }
  }


  return CC;
}
