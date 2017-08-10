#define MAX_N 10000

property_r vec_bound(matrix<uint> V, uint to) :
  forall(fi)((0 <= fi < to<o>) -> (V<o>[fi] <= fi));

property_r large_error_r(matrix<uint> x, uint v) :
  forall(fi)((0 <= fi < v<r>) -> (x<r>[fi] == x<o>[fi] || fi < x<r>[fi]));

property_r outer_spec(uint to,
                      uint N,
                      matrix<uint> next_CC,
                      matrix<uint> CC,
                      matrix<uint> adj) :
  forall(fi)((0 <= fi < to) ->
      (forall(fj)((0 <= fj < N && adj[fi][fj] == 1) -> next_CC[fi] <= CC[fj]) &&
       next_CC[fi] <= CC[fi] &&
       (exists(ej)(next_CC[fi] == CC[ej] && 0 <= ej < N && adj[fi][ej] == 1) ||
        next_CC[fi] == CC[fi])));

property_r inner_spec(uint to,
                      uint v,
                      uint N,
                      matrix<uint> next_CC,
                      matrix<uint> CC,
                      matrix<uint> adj) :
  forall(fi)((0 <= fi < to && adj[v][fi] == 1) -> next_CC[v] <= CC[fi]) &&
  next_CC[v] <= CC[v] &&
  (exists(ei)(next_CC[v] == CC[ei] && 0 <= ei < N && adj[v][ei] == 1) ||
   next_CC[v] == CC[v]);

requires N < MAX_N
r_requires eq(adj)
matrix<uint> cc(uint N, matrix<uint> adj(N, N)) {
  // Helpers
  matrix<uint> CC(N);
  @region(unreliable) matrix<uint> next_CC(N);

  // Line 1: for each v in V do
  for (uint v = 0; v < N; ++v) (1 == 1) (vec_bound(CC, v)) {
    // Line 2: CC^1[v] = v;
    //         CC^0[v] = v;
    //         P*[v] = -1;
    CC[v] = v;
  }

  // Line 4: N_s = |V|
  uint N_s = N;

  // Line 5: while N_s > 0 do:
  //while (0 < N_s) (1 == 1) (1 == 1) {
  @noinf while (0 < N_s)
        (N < MAX_N)
        (eq(N) && eq(adj) && eq(N_s) && eq(CC) && vec_bound(CC, N)) {
    // Line 6: MemCpy(CC^i, CC^{i-1}, |V|)
    for (uint v = 0; v < N; ++v)
        (1 == 1)
        (large_error_r(next_CC, v) &&
         forall(fi)((0 <= fi < v<o>) -> next_CC<o>[fi] == CC<o>[fi])) {
      fwrite(next_CC[v], CC[v]);
    }

    N_s = 0;

    // Line 7: for each v in V do
    for (uint v = 0; v < N; ++v)
        (1 == 1)
        (vec_bound(next_CC, N) &&
         forall(fi)((v<o> <= fi < N<o>) -> next_CC<o>[fi] == CC<o>[fi]) &&
         outer_spec(v<o>, N<o>, next_CC<o>, CC<o>, adj<o>) &&
         large_error_r(next_CC, N)) {
      // Line 8: for each u in adj(v) do:

      for (uint j = 0; j < N; ++j)
          (v < N && N < MAX_N)
          (forall(fi)((v<o> < fi < N<o>) -> next_CC<o>[fi] == CC<o>[fi]) &&
           inner_spec(j<o>, v<o>, N<o>, next_CC<o>, CC<o>, adj<o>) && eq(j)) {

        // Line 9: if CC^{i-1}[u] < CC^{i}[v] then
        // At this point next_CC[v] == CC[v], so we use CC[v] for the
        // conditional and track N_s here.
        if (CC[j] < next_CC[v] && next_CC[v] <= v && adj[v][j] == 1) {
          // Line 10: CC^i[v] = CC^{i-1}[u]
          fwrite(next_CC[v], CC[j]);
        }
      }
    }
    // Fault detection and correction (reliable)

    // Line 13: for each v in V do
    matrix<uint> corrected_next_CC(N);
    @noinf for (uint v = 0; v < N; ++v)
        (1 == 1)
        (outer_spec(v<r>, N<r>, corrected_next_CC<r>, CC<r>, adj<r>) &&
         eq(N) && eq(CC) && eq(adj) && eq(v) &&
         forall(fi)(((0 <= fi < v<r>) -> (corrected_next_CC<r>[fi] == corrected_next_CC<o>[fi]))) &&
         eq(N_s) &&
         vec_bound(next_CC, N) &&
         large_error_r(next_CC, N) &&
         outer_spec(N<o>, N<o>, next_CC<o>, CC<o>, adj<o>)) {

      if (next_CC[v] <= v) {
        corrected_next_CC[v] = next_CC[v];
      } else {
        corrected_next_CC[v] = CC[v];
        // Line 16: for each u in adj(v) do
        for (uint j = 0; j < N; ++j)
            (v < N && v < next_CC[v])
            (inner_spec(j<r>, v<r>, N<r>, corrected_next_CC<r>, CC<r>, adj<r>)) {
          //  Line 17: if CC^{i-1}[u] < CC^i[v] then
          if (CC[j] < corrected_next_CC[v] && adj[v][j] == 1) {
            // Line 18: CC^i[v] = CC^{i-1}[u]
            corrected_next_CC[v] = CC[j];
          }
        }
      }

      if (corrected_next_CC[v] < CC[v]) { ++N_s; }
    }

    CC = corrected_next_CC;
  }

  return CC;
}
