#define MAX_N 10000

property_r vec_bound(matrix<uint> V, uint to) :
  forall(uint fi)(fi < to<o> -> (V<o>[fi] <= fi));

property_r large_error_r(matrix<uint> x, uint v) :
  forall(uint fi)(fi < v<r> -> (x<r>[fi] == x<o>[fi] || fi < x<r>[fi]));

property_r outer_spec(uint to,
                      uint N,
                      matrix<uint> next_CC,
                      matrix<uint> CC,
                      matrix<uint> adj) :
  forall(uint fi)(fi < to ->
      (forall(uint fj)((fj < N && adj[fi][fj] == 1) -> next_CC[fi] <= CC[fj]) &&
       next_CC[fi] <= CC[fi] &&
       (exists(uint ej)(next_CC[fi] == CC[ej] && ej < N && adj[fi][ej] == 1) ||
        next_CC[fi] == CC[fi])));

property_r inner_spec(uint to,
                      uint v,
                      uint N,
                      matrix<uint> next_CC,
                      matrix<uint> CC,
                      matrix<uint> adj) :
  forall(uint fi)((fi < to && adj[v][fi] == 1) -> next_CC[v] <= CC[fi]) &&
  next_CC[v] <= CC[v] &&
  (exists(uint ei)(next_CC[v] == CC[ei] && ei < N && adj[v][ei] == 1) ||
   next_CC[v] == CC[v]);

requires N < MAX_N
r_requires eq(adj)
matrix<uint> cc(uint N, matrix<uint> adj(N, N)) {
  // Helpers
  matrix<uint> CC(N);
  @region(unreliable) matrix<uint> next_CC(N);

  // Line 1: for each v in V do
  @label(init) for (uint v = 0; v < N; ++v) (1 == 1) (vec_bound(CC, v)) {
    // Line 2: CC^1[v] = v;
    //         CC^0[v] = v;
    //         P*[v] = -1;
    CC[v] = v;
  }

  // Line 4: N_s = |V|
  uint N_s = N;

  // Line 5: while N_s > 0 do:
  //while (0 < N_s) (1 == 1) (1 == 1) {
  @noinf @label(outer_while) while (0 < N_s)
        (N < MAX_N)
        (eq(N) && eq(adj) && eq(N_s) && eq(CC) && vec_bound(CC, N)) {
    // Line 6: MemCpy(CC^i, CC^{i-1}, |V|)
    next_CC = CC;

    N_s = 0;

    model.reliable = false;

    // Line 7: for each v in V do
    @label(outer_faulty)
    for (uint v = 0; v < N; ++v)
        (1 == 1)
        (vec_bound(next_CC, N) &&
         forall(uint fi)((v<o> <= fi < N<o>) -> next_CC<o>[fi] == CC<o>[fi]) &&
         outer_spec(v<o>, N<o>, next_CC<o>, CC<o>, adj<o>) &&
         large_error_r(next_CC, N)) {
      // Line 8: for each u in adj(v) do:

      @label(inner_faulty)
      for (uint j = 0; j < N; ++j)
          (v < N && N < MAX_N)
          (forall(uint fi)((v<o> < fi < N<o>) -> next_CC<o>[fi] == CC<o>[fi]) &&
           inner_spec(j<o>, v<o>, N<o>, next_CC<o>, CC<o>, adj<o>)) {

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

    model.reliable = true;

    // TODO: Make a spec var
    matrix<uint> old_next_CC(N);
    old_next_CC = next_CC;

    // TODO: Try exact same scenario as copy version but with corrected_next_CC
    // substituted by next_CC and next_CC substitued by old_next_CC.  Then,
    // convert over one by one

    // TODO: Disable inference on the inner correction loop for easier
    // debugging.

    // Line 13: for each v in V do
    @noinf @label(outer_correction) for (uint v = 0; v < N; ++v)
        (1 == 1)
        (outer_spec(v<r>, N<r>, next_CC<r>, CC<r>, adj<r>) &&
         eq(N) && eq(CC) && eq(adj) &&
         forall(uint fi)((fi < v<r> -> (next_CC<r>[fi] == next_CC<o>[fi]))) &&
         eq(N_s) && eq(v) &&
         vec_bound(old_next_CC, N) &&
         large_error_r(old_next_CC, N) &&
         outer_spec(N<o>, N<o>, old_next_CC<o>, CC<o>, adj<o>)) {

      next_CC[v] = old_next_CC[v];
      if (v < old_next_CC[v]) {
        // TODO: Use fwrites here
        next_CC[v] = CC[v];
        // Line 16: for each u in adj(v) do
        @label(inner_correction) for (uint j = 0; j < N; ++j)
            (v < old_next_CC[v])
            (inner_spec(j<r>, v<r>, N<r>, next_CC<r>, CC<r>, adj<r>)) {
          //  Line 17: if CC^{i-1}[u] < CC^i[v] then
          if (CC[j] < next_CC[v] && adj[v][j] == 1) {
            // Line 18: CC^i[v] = CC^{i-1}[u]
            next_CC[v] = CC[j];
          }
        }
      }

      if (next_CC[v] < CC[v]) { ++N_s; }
    }

    CC = next_CC;
  }

  return CC;
}
