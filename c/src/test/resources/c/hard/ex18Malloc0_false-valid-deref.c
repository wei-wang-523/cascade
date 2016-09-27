#include "../../../reserved.h"

int main(){
  
  int * a;
  int i,j;
  int k = __VERIFIER_nondet_int();
  
  if ( k < 1 ) k = 1;
  
  a= malloc( k * sizeof(int));
  
  ASSUME(k >= 100);
  
  for (i =0 ; i != k; i++) {
    if (a[i] <= 1)
      break;
  }
  i--;
  
  free(a);
  return 0;
  
}