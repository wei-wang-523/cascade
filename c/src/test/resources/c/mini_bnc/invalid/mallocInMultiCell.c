typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int * main (int x){ //  mini bnc for ex18.c and ex7.c
	ASSUME(x > 0);
	
	int * a = (int *) malloc( x * sizeof(int));
	int i = 0;	
	a[i] = 1;

//  valid in single-cell encoding, x *n sizeof(int) = x > 0
//  invalid in multi-cell encoding since sizeof(int) = 4, sizeof(int) *n x == 4 *n x == 0
	return a;
}