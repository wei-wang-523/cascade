typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int main() {
	
	int flag;
	int * a;
	
	if (flag){
		a = (int *) malloc(5 * sizeof(int));
	} else {
		a = (int *) malloc(5 * sizeof(int));
	}
	
	a[0] = 1;
  free(a);
	return 1;
}

// The loop invariant will fail with partition memory model, but lambda parition will pass