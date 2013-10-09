
int * main (int x, int y){
	
	int * a;
	int i = 0;
	
	if ( x< 0 || y < 0 || y > x ) return (int *) 0;
	
	a = (int *) malloc( x * sizeof(int));
	
	if (a == 0 ) exit(1);
	
	ASSERT(valid(&a[i]));
	a[i] = 0;
	
	return a;
}