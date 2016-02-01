int main() {
	
	int flag;
	int * a;
	
	if (flag){
		a = (int *) malloc(5 * sizeof(int));
	} else {
		a = (int *) malloc(5 * sizeof(int));
	}
	ASSUME(a);
	
	ASSERT(valid(&a[0]));
	
	return 1;
}

// The loop invariant will fail with partition memory model, but lambda parition will pass