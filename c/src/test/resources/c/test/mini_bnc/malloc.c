//#include "stdlib.h"

int main() {
  int * p, a;
  p = (int *)malloc(2*sizeof(int));
//  ASSUME(valid_malloc(p, 2*sizeof(int)));
//  ASSUME(p != 0);
//  ASSERT(valid(&p[1]));
  a = p[1];
//  ASSERT(valid_free(p));
  free(p);
  return p[1];
}
