typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int * main (int x){

	ASSUME(x >= 0);	
	int * a = (int *) malloc( x * sizeof(int));
	int i = 0;
	a[i] = __NONDET__();
	i = __NONDET__();
	
	ASSUME(i >= 0 && i < x);
	
	return a;
}