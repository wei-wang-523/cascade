#include "../../../reserved.h"

typedef struct {
  int a;
  int b;
} f_t;

int bar(f_t * w, int n){
  w[0].a=-1;
  w[0].b=-2;
  return 1;
}

int foo(int * y, int n){
  y[0]=-1;
  return 1;
}

int main(){
  
  f_t * x, *z;
  int * y, *w;
  int n;
  n = __VERIFIER_nondet_int();
  x = (f_t*) malloc(n * sizeof(f_t));
  y = (int *) x;
  foo(y,2*n);
  w = (int *) malloc( 2*n * sizeof(int));
  z = (f_t*) w;
  bar(z,n);
  return 1;
}

// Valid. Burstall returns invalid at checking valid(y) in foo
// With type casting between tag(0)(f_t) and int in the statement
// "y = (int *) x", check valid(y) will look at int's equivalent class
// not in tag(0)(f_t)'s, and no region is allocated in int.