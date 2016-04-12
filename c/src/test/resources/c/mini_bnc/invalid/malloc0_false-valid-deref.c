#include "../../../reserved.h"

int main (int x){

	ASSUME(x >= 0);	
	int * a = (int *) malloc( x * sizeof(int));
	int i = 0;
	a[i] = __VERIFIER_nondet_int();
	i = __VERIFIER_nondet_int();
	
	ASSUME(i >= 0 && i < x);
	
	return 0;
}