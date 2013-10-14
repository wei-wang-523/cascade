int * main (int x, int y){

	ASSUME(x >= 0 && y >= 0 && x >= y );
	
	int * a = (int *) malloc( x * sizeof(int));
	ASSUME(a != (int*) 0 );
	
	int i = 0;
	a[i] = __NONDET__();
	i = __NONDET__();
	
	ASSUME(i >= 0 && i < y);
	ASSERT(valid(&a[i]));
	
	return a;
}