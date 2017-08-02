#define MAX_N 10000

property mat_bound(matrix<real> A, int max) :
  forall(fi)(forall(fj)(0 <= A[fi][fj] < max));

property vec_bound(matrix<real> V, int to) :
  forall(fi)((0 <= fi < to) -> (0 <= V[fi] <= fi));

property_r vec_bound_r(matrix<real> V, int to) :
  forall(fi)((0 <= fi < to<r>) -> (0 <= V<r>[fi] <= fi));

property_r vec_bound_o(matrix<real> V, int to) :
  forall(fi)((0 <= fi < to<o>) -> (0 <= V<o>[fi] <= fi));

property_r large_error_r(matrix<real> x, int v) :
  forall(fi)((0 <= fi < v<r>) -> (x<r>[fi] == x<o>[fi] || fi < x<r>[fi] || x<r>[fi] < 0));

  // TODO: Break apart these foralls and exists.
  // For example, next_CC<o>[fi] == CC<o>[fi] doesn't need to be under exists
property_r next_CC_spec(int to,
                        int N,
                        matrix<real> next_CC,
                        matrix<real> CC,
                        matrix<real> adj) :
  forall(fi)(forall(fj)(((0 <= fi < to<o>) && (0 <= fj < adj<o>[fi][N<o>])) ->
      (next_CC<o>[fi] <= CC<o>[adj<o>[fi][fj]] &&
       next_CC<o>[fi] <= CC<o>[fi]))) &&
  forall(fi)(exists(fj)((0 <= fi < to<o>) ->
      ((next_CC<o>[fi] == CC<o>[adj<o>[fi][fj]] &&
        0 <= fj < adj<o>[fi][N<o>]) ||
        next_CC<o>[fi] == CC<o>[fi])));

property_r corrected_CC_spec(int to,
                             int N,
                             matrix<real> next_CC,
                             matrix<real> corrected_CC,
                             matrix<real> CC,
                             matrix<real> adj) :
  forall(fi)(forall(fj)(((0 <= fi < to<o>) &&
                         (0 <= fj < adj<o>[fi][N<o>]) &&
                         (!(0 <= next_CC<r>[fi] <= fi))) ->
      (corrected_CC<r>[fi] <= CC<o>[adj<o>[fi][fj]] &&
       corrected_CC<r>[fi] <= CC<o>[fi]))) &&
  forall(fi)(exists(fj)(((0 <= fi < to<o>) && (!(0 <= next_CC<r>[fi] <= fi)))->
      ((corrected_CC<r>[fi] == CC<o>[adj<o>[fi][fj]] &&
        0 <= fj < adj<o>[fi][N<o>]) ||
        corrected_CC<r>[fi] == CC<o>[fi])));

property_r inner_next_CC_spec(int to,
                              int v,
                              matrix<real> next_CC,
                              matrix<real> CC,
                              matrix<real> adj) :
  forall(fi)((0 <= fi < to<o>) -> (next_CC<o>[v<o>] <= CC<o>[adj<o>[v<o>][fi]] &&
                                next_CC<o>[v<o>] <= CC<o>[v<o>])) &&
  exists(ei)((next_CC<o>[v<o>] == CC<o>[adj<o>[v<o>][ei]] &&
              0 <= ei < adj<o>[v<o>][N<o>]) ||
              next_CC<o>[v<o>] == CC<o>[v<o>]);

property_r inner_corrected_CC_spec(int g,
                                   int v,
                                   matrix<real> corrected_CC,
                                   matrix<real> CC,
                                   matrix<real> adj) :
  forall(fi)((0 <= fi < g<r>) -> corrected_CC<r>[v<r>] <= CC<o>[adj<o>[v<o>][fi]]) &&
  corrected_CC<r>[v<r>] <= CC<o>[v<o>] &&
  exists(ei)((corrected_CC<r>[v<r>] == CC<o>[adj<o>[v<o>][ei]] &&
             0 <= ei < adj<o>[v<o>][N<o>]) ||
            corrected_CC<r>[v<r>] == CC<o>[v<o>]);

requires N < MAX_N && mat_bound(adj, N)
r_requires eq(adj)
matrix<int> cc(int N, matrix<int> adj(N, N+1)) {
  // Helpers
  matrix<int> CC(N);
  @region(unreliable) matrix<int> next_CC(N);
  matrix<int> corrected_next_CC(N);
  matrix<int> P_star(N);

  // Line 1: for each v in V do
  for (int v = 0; v < N; ++v) (vec_bound(CC, v)) (1 == 1) {
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
  //while (0 < N_s) (1 == 1) (1 == 1) {
  // TODO: Get eq(CC) in outer while?
  @noinf while (0 < N_s)
               (N < MAX_N && mat_bound(adj, N) && vec_bound(CC, N))
               (eq(N) && eq(N_s) && eq(adj) && eq(CC)) {
    // Line 6: MemCpy(CC^i, CC^{i-1}, |V|)
    for (int v = 0; v < N; ++v)
        (0 <= v <= N && vec_bound(CC, N))
        (large_error_r(next_CC, v) &&
         vec_bound_o(next_CC, v) &&
         forall(fi)((0 <= fi < v<o>) -> next_CC<o>[fi] == CC<o>[fi])) {
      next_CC[v] = CC[v];
    }

    N_s = 0;

    // Line 7: for each v in V do
    @noinf for (int v = 0; v < N; ++v)
        (0 <= v <= N && vec_bound(CC, N) && mat_bound(adj, N))
        (large_error_r(next_CC, N) &&
         eq(N_s) &&
         vec_bound_o(next_CC, N) &&
         forall(fi)((0 <= fi < N<o>) -> next_CC<o>[fi] <= CC<o>[fi]) &&
         forall(fi)((v<o> <= fi < N<o>) -> next_CC<o>[fi] == CC<o>[fi]) &&
         next_CC_spec(v, N, next_CC, CC, adj) &&
         eq(N) && eq(CC) && eq(adj) && eq(v)) {
      // Line 8: for each u in adj(v) do:

      // TODO: Try to get rid of this assertion (for some reason removing it
      // makes the path checking for the if inside hang?)
      relational_assert(next_CC<o>[v<o>] == CC<o>[v<o>]);


      // TODO: Path checking gets hung up here in leto, but not with the
      // serialized version.  Try adding a timeout in leto.
      @noinf for (int j = 0; j < adj[v][N]; ++j)
          (0 <= j <= N && 0 <= v < N && vec_bound(CC, N) && N < MAX_N && mat_bound(adj, N))
          (large_error_r(next_CC, N) &&
           eq(N_s) &&
           vec_bound_o(next_CC, N) &&
           next_CC<o>[v<o>] <= CC<o>[v<o>] &&
           eq(j) && eq(N) && eq(CC) && eq(adj) && eq(v) &&
           forall(fi)((0 <= fi < N<o>) -> next_CC<o>[fi] <= CC<o>[fi]) &&
           forall(fi)((v<o> < fi < N<o>) -> next_CC<o>[fi] == CC<o>[fi]) &&
           inner_next_CC_spec(j, v, next_CC, CC, adj) &&
           next_CC_spec(v, N, next_CC, CC, adj)) {
        int u = adj[v][j];

        // Line 9: if CC^{i-1}[u] < CC^{i}[v] then
        // At this point next_CC[v] == CC[v], so we use CC[v] for the
        // conditional and track N_s here.
        if (CC[u] < next_CC[v] && 0 <= next_CC[v] <= v) {
          // Line 10: CC^i[v] = CC^{i-1}[u]
          next_CC[v] = CC[u];

          // Line 11: P*[v] = &u
          P_star[v] = j;
        }
      }
    }


    // Fault detection and correction (reliable)

    // Line 13: for each v in V do
    @noinf for (int v = 0; v < N; ++v)
               (0 <= v <= N && vec_bound(CC, N) && mat_bound(adj, N))
               (large_error_r(next_CC, N) &&
                corrected_CC_spec(v, N, next_CC, corrected_next_CC, CC, adj) &&
                eq(N) && eq(CC) && eq(adj) && eq(v)) {

      corrected_next_CC[v] = CC[v];

      // Line 16: for each u in adj(v) do
      for (int j = 0; j < adj[v][N] && (next_CC[v] < 0 ||  v < next_CC[v]); ++j)
          (0 <= v < N && vec_bound(CC, N) && 0 <= j <= N)
          (inner_corrected_CC_spec(j , v, corrected_next_CC, CC, adj)) {
        int u = adj[v][j];

        //  Line 17: if CC^{i-1}[u] < CC^i[v] then
        if (CC[u] < corrected_next_CC[v]) {
          // Line 18: CC^i[v] = CC^{i-1}[u]
          corrected_next_CC[v] = CC[u];

          // Line 19: P*[v] = &u
          P_star[v] = j;
        }
      }
    }

    // Line 22: i = i + 1
    ++i;

    matrix<int> merged_CC(N);

    // Update CC (merge results)
    @noinf for (int v = 0; v < N; ++v)
        (vec_bound(CC, N) && 0 <= v <= N)
        (eq(v) &&
         eq(N) &&
         eq(merged_CC) &&
         eq(CC) &&
         eq(N_s) &&
         vec_bound_o(next_CC, N) &&
         (forall(fi)(((0 <= fi < N<r>) && (!(0 <= next_CC<r>[fi] <= fi))) -> (corrected_next_CC<r>[fi] == next_CC<o>[fi]))) &&
         large_error_r(next_CC, N)) {
      if (0 <= next_CC[v] <= v) {
        merged_CC[v] = next_CC[v];
      } else {
        merged_CC[v] = corrected_next_CC[v];
      }

      if (merged_CC[v] < CC[v]) { ++N_s; }
    }

    CC = merged_CC;
  }


  return CC;
}
