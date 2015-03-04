extern int __VERIFIER_nondet_int();
int * a;
int n;

int test(){
	
	int i;
	
	for (i = 0; i < n; ++i){
		ASSERT(valid(&a[i]));
		if (a[i])
			n--;
		
		a[i] = 0;
		
		
	}
	
	return 0;
}


int main(){
	
	n = __VERIFIER_nondet_int();
	
	if (n <= 0 || n >= 1024){
		n=5;
		a = (int *) malloc(n * sizeof(int));
	} else {
		a = (int *) malloc( n * sizeof(int));
	}
	
	ASSUME(a);
	
	test();
	
	return 1;
}
