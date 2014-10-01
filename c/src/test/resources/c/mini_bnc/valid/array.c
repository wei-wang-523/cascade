int main() {
  int A[3][3] = {{1,2,3}, {1,0,1}, {0,2,1}};
  A[1][1] = 1;
  ASSERT(valid(&A[2][2]));
  ASSERT(valid(&A[2]));
  ASSERT(valid(&A));
  ASSERT(valid(A));
  ASSERT(A[1][1] == 1 && A[2][2] == 1);
  return A[1][1];
}
