extern int __VERIFIER_nondet_int();
int * a;


int test(int * n ){
	
	int i;
	
	for (i = 0; i < (*n); ++i){
		ASSERT(valid(&a[i]));
		a[i] = 0;
		
		
	}
	
	return 1;
}


int main(){
	
	int n = __VERIFIER_nondet_int();
	
	if (n <= 0 || n >= 1024){
		exit(1);
	} else {
		a = (int *) malloc( n * sizeof(int));
	}
	
	ASSUME(a);
	
	test(&n);
	
	return 1;
}
