#include "../../../reserved.h"

typedef struct foo{
  
  int x;
  int z;
  
} foo_t;


int main(int n){
  ASSUME(n > 1);
  foo_t * a, a1;
  int * b;
  a = (foo_t*) malloc(n * sizeof(foo_t));
  
  b = (int *)a; /*-- down casting. Length(b) = 2 * Length(a) --*/
  b[2*n -1 ] = '\0';
  
  free(a);
  return 1;
}