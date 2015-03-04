extern int __VERIFIER_nondet_int();
int main(){
	
	int * a;
	int k = __VERIFIER_nondet_int();
	int i;
	if ( k <= 0 ) return -1;
	
	a= malloc( k * sizeof(int));
	
	for (i =0 ; i != k; i++) {
		ASSERT(valid(&a[i]));
		if (a[i]) return 1;
	}
	
	return 0;
	
}