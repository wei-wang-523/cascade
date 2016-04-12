#include "../../../reserved.h"

int main()
{
  int B[5];
  int *p = B;
  int *q = &B;
  int idx;
  ASSUME(idx >= 0 && idx < 5);
  B[idx] = 5;
  p[idx] = 4;
  q[idx] = 3;
}