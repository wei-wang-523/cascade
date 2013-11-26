int * a;
int n;

int test(){
	
	int i;
	// First statement is in the loop scope
	for (i = 0; i < n; ++i) 
	INVARIANT(valid(&a[i])); {
		a[i] = 0;		
	}
	
	return 0;
}


int main(){
	
	n = __NONDET__();
	
	if (n <= 0 || n >= 1024){
		n=5;
		a = (int *) malloc(n * sizeof(int));
	} else {
		a = (int *) malloc(n * sizeof(int));
	}
	ASSUME(a != (int *) 0);
	// Previous statement is in the if-else scope
	// Call statement is required to indicate the scope of call node
	test();
	
	return 1;
}