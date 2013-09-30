//#include "stdlib.h"

int main() {
  int * p, a;
  p = (int *)malloc(2*sizeof(int));
  ASSUME(p != 0);
  ASSERT(valid(&p[1]));
  a = p[1];
  free(p);
  return p[1];
}
