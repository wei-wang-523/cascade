
int main(){
	
	int * a;
	int i,j;
	int k = __NONDET__();
	
	if ( k <= 0 ) 
		return -1;
	a= malloc( k * sizeof(int));
	
	ASSUME(a);
	ASSUME(k >= 100);
	
	for (i =0 ; i != k; i++) {
		ASSERT(valid(&a[i]));
		if (a[i] <= 1) 
			break;
	}
	ASSERT(forall(idx_0, idx_1, implies(0 <= idx_0 && idx_0 < i, a[idx_0] > 1)));
	i--;
	
	for (j = 0; j < i; ++j) {
		ASSERT(valid(&a[j]));
		a[j] = a[i];
	}
	ASSERT(forall(idx, implies(0 <= idx && idx < i, a[idx] == a[i])));
	return 0;
	
}