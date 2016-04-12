#include "../../../reserved.h"

int main (int x){ //  mini bnc for ex18.c and ex7.c
	int * a = (int *) malloc( x * sizeof(int));
	int i = 0;	
	a[i] = 1;
  free(a);
//  valid in single-cell encoding, x *n sizeof(int) = x > 0
//  invalid in multi-cell encoding since sizeof(int) = 4, sizeof(int) *n x == 4 *n x == 0
	return 0;
}