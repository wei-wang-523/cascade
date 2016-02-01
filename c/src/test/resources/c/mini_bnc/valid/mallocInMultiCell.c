int * main (int x){ //  mini bnc for ex18.c and ex7.c
	ASSUME(x > 0);
	
	int * a = (int *) malloc( x * sizeof(int));
	ASSUME(a != (int*) 0 );
	
	int i = 0;	
	ASSERT(valid(&a[i]));

//  valid in single-cell encoding, x *n sizeof(int) = x > 0
//  invalid in multi-cell encoding since sizeof(int) = 4, sizeof(int) *n x == 4 *n x == 0
	return a;
}