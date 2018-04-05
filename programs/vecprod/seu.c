property_r bounded_error(matrix<real> v, uint i) :
  exists(uint ei)
    (forall(uint fi)((fi < i<r> && fi != ei) -> v<o>[fi] == v<r>[fi]));

uint N;
matrix<int> x(N);
matrix<int> y(N);
matrix<int> result(N);

@label(loop)
for (uint i = 0; i < N; ++i)
    (1 == 1)
    ((model.upset == false -> eq(result)) &&
     (model.upset == true -> bounded_error(result, i))) {
  result[i] = x[i] *. y[i];
}

relational_assert(bounded_error(result, N));
