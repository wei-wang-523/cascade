#include "../../../reserved.h"

int main()
{
  int B[3][2] = {0, 1};
  int *p = B;
  int *q = B[0];
  int *k = &B;
  int *m = &B[0];
  p[1] = 2;
  B[0][1] = 3;
  *(1 + *(B+1)) = 4;
  
  int* C[10];
  C[0] = (int*) malloc(sizeof(int));
  C[1] = (int*) malloc(sizeof(int));
  *(C[0]) = 2;
  
  free(C[0]);
  free(C[1]);
  return 1;
}