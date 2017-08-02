#define MAX_N 10000

property vec_bound(matrix<real> V, int to) :
  forall(fi)((0 <= fi < to) -> (0 <= V[fi] <= fi));

property_r vec_bound_r(matrix<real> V, int to) :
  forall(fi)((0 <= fi < to<r>) -> (0 <= V<r>[fi] <= fi));

property_r vec_bound_o(matrix<real> V, int to) :
  forall(fi)((0 <= fi < to<o>) -> (0 <= V<o>[fi] <= fi));

property_r large_error_r(matrix<real> x, int v) :
  forall(fi)((0 <= fi < v<r>) ->
      (x<r>[fi] == x<o>[fi] || fi < x<r>[fi] || x<r>[fi] < 0));

property_r next_CC_spec(int to,
                        int N,
                        matrix<real> next_CC,
                        matrix<real> CC,
                        matrix<real> adj) :
  forall(fi)((0 <= fi < to<o>) ->
      (forall(fj)((0 <= fj < N<o> && adj<o>[fi][fj] == 1) ->
           next_CC<o>[fi] <= CC<o>[fj]) &&
       next_CC<o>[fi] <= CC<o>[fi] &&
       (exists(ej)(next_CC<o>[fi] == CC<o>[ej] &&
                   0 <= ej < N<o> &&
                   adj<o>[fi][ej] == 1) ||
        next_CC<o>[fi] == CC<o>[fi])));

property_r corrected_CC_spec(int to,
                             int N,
                             matrix<real> next_CC,
                             matrix<real> corrected_CC,
                             matrix<real> CC,
                             matrix<real> adj) :
  forall(fi)((0 <= fi < to<o> && (!(0 <= next_CC<r>[fi] <= fi))) ->
      (forall(fj)((0 <= fj < N<o> && adj<o>[fi][fj] == 1) ->
           corrected_CC<r>[fi] <= CC<o>[fj]) &&
       corrected_CC<r>[fi] <= CC<o>[fi] &&
       (exists(ej)(corrected_CC<r>[fi] == CC<o>[ej] &&
                   0 <= ej < N<o> &&
                   adj<o>[fi][ej] == 1) ||
        corrected_CC<r>[fi] == CC<o>[fi])));


property_r inner_next_CC_spec(int to,
                              int v,
                              matrix<real> next_CC,
                              matrix<real> CC,
                              matrix<real> adj) :
  forall(fi)((0 <= fi < to<o> && adj<o>[v<o>][fi] == 1) ->
      next_CC<o>[v<o>] <= CC<o>[fi]) &&
  next_CC<o>[v<o>] <= CC<o>[v<o>] &&
  (exists(ei)(next_CC<o>[v<o>] == CC<o>[ei] &&
              0 <= ei < N<o> &&
              adj<o>[v<o>][ei] == 1) ||
   next_CC<o>[v<o>] == CC<o>[v<o>]);

property_r inner_corrected_CC_spec(int g,
                                   int v,
                                   matrix<real> corrected_CC,
                                   matrix<real> CC,
                                   matrix<real> adj) :
  forall(fi)((0 <= fi < g<r> && adj<o>[v<o>][fi] == 1) ->
      corrected_CC<r>[v<r>] <= CC<o>[fi]) &&
  corrected_CC<r>[v<r>] <= CC<o>[v<o>] &&
  (exists(ei)(corrected_CC<r>[v<r>] == CC<o>[ei] &&
              0 <= ei < N<o> &&
              adj<o>[v<o>][ei] == 1) ||
corrected_CC<r>[v<r>] == CC<o>[v<o>]);


requires N < MAX_N
r_requires eq(adj)
matrix<int> cc(int N, matrix<int> adj(N, N)) {
  // Helpers
  matrix<int> CC(N);
  @region(unreliable) matrix<int> next_CC(N);
  matrix<int> corrected_next_CC(N);

  // Line 1: for each v in V do
  for (int v = 0; v < N; ++v) (vec_bound(CC, v)) (1 == 1) {
    // Line 2: CC^1[v] = v;
    //         CC^0[v] = v;
    //         P*[v] = -1;
		fwrite(next_CC[v], v);
    CC[v] = v;
  }

  // Line 3: i = 1;
  int i = 1;

  // Line 4: N_s = |V|
  int N_s = N;

  // Line 5: while N_s > 0 do:
  //while (0 < N_s) (1 == 1) (1 == 1) {
  // TODO: Get eq(CC) in outer while?
  @noinf while (0 < N_s)
               (N < MAX_N && vec_bound(CC, N))
               (eq(N) && eq(N_s) && eq(adj) && eq(CC)) {
    // Line 6: MemCpy(CC^i, CC^{i-1}, |V|)
    for (int v = 0; v < N; ++v)
        (1 == 1)
        (large_error_r(next_CC, v) &&
         forall(fi)((0 <= fi < v<o>) -> next_CC<o>[fi] == CC<o>[fi])) {
      fwrite(next_CC[v], CC[v]);
    }

    N_s = 0;

    // Line 7: for each v in V do
    @noinf for (int v = 0; v < N; ++v)
        (1 == 1)
        (large_error_r(next_CC, N) &&
         vec_bound_o(next_CC, N) &&
         forall(fi)((v<o> <= fi < N<o>) -> next_CC<o>[fi] == CC<o>[fi]) &&
         next_CC_spec(v, N, next_CC, CC, adj) &&
         eq(N) && eq(CC) && eq(adj) && eq(v)) {
      // Line 8: for each u in adj(v) do:


      // TODO: Path checking gets hung up here in leto, but not with the
      // serialized version.  Try adding a timeout in leto.
      @noinf for (int j = 0; j < N; ++j)
          (0 <= j <= N && 0 <= v < N && N < MAX_N)
          (large_error_r(next_CC, N) &&
           vec_bound_o(next_CC, N) &&
           eq(j) && eq(N) && eq(CC) && eq(adj) && eq(v) &&
           forall(fi)((v<o> < fi < N<o>) -> next_CC<o>[fi] == CC<o>[fi]) &&
           inner_next_CC_spec(j, v, next_CC, CC, adj) &&
           next_CC_spec(v, N, next_CC, CC, adj)) {

        // Line 9: if CC^{i-1}[u] < CC^{i}[v] then
        // At this point next_CC[v] == CC[v], so we use CC[v] for the
        // conditional and track N_s here.
        if (CC[j] < next_CC[v] && 0 <= next_CC[v] <= v && adj[v][j] == 1) {
          // Line 10: CC^i[v] = CC^{i-1}[u]
          fwrite(next_CC[v], CC[j]);
        }
      }
    }

    // Fault detection and correction (reliable)

    // Line 13: for each v in V do
    @noinf for (int v = 0; v < N; ++v)
               (1 == 1)
               (corrected_CC_spec(v, N, next_CC, corrected_next_CC, CC, adj) &&
                eq(N) && eq(CC) && eq(adj) && eq(v)) {

      corrected_next_CC[v] = CC[v];

      // Line 16: for each u in adj(v) do
      for (int j = 0; j < N && (next_CC[v] < 0 ||  v < next_CC[v]); ++j)
          (0 <= v < N && 0 <= j <= N)
          (inner_corrected_CC_spec(j , v, corrected_next_CC, CC, adj)) {
        //  Line 17: if CC^{i-1}[u] < CC^i[v] then
        if (CC[j] < corrected_next_CC[v] && adj[v][j] == 1) {
          // Line 18: CC^i[v] = CC^{i-1}[u]
          corrected_next_CC[v] = CC[j];
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
