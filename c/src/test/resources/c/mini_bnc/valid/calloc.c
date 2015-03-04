typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int * main (){
	int * a = (int *) calloc(2, sizeof(int));
	a[0] = 1;
	ASSERT(a[1] == 0);
	ASSERT(a[0] == 1);
  free(a);
	return a;
}