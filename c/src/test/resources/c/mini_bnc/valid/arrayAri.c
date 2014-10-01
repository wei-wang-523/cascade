int C[2];
int a = 3;
int main() 
{
  int B[3] = {1, 1, 1}; 
  int A[6]; 

  B[0] = A[0] + A[1];
  ASSERT(B[0] == A[0] + A[1]);
  return B[0];
}
