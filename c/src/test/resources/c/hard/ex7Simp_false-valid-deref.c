#include "../../../reserved.h"

int main (int x){
	
	int * a;
  
  if (x < 1) x = 1;
  
	a = (int *) malloc( x * sizeof(int));
	
  for(int i = 0; i < x; i++) {
    a[i] = 1;
  }
  
  free(a);
	return 0;
	
}

// test forall formula in assertion with valid predicate.
// design for lambda encoding, to test if both z3 and cvc4
// can handle quantified formula parsed via CExpressionEncoder properly