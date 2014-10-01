int * main (int x){

//	ASSUME(x >= 0);
	
	int * a = (int *) malloc( x * sizeof(int));
	ASSUME(a != (int*) 0 );
	
	int i = 0;
	a[i] = __NONDET__();
	i = __NONDET__();
	
	ASSUME(i >= 0 && i < x);
	ASSERT(valid(&a[i]));
	
	return a;
}