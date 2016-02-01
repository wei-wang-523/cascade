typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int main(int i, int *s) {
	s = (int *)malloc(5*sizeof(int));
	if(i <= 0 ) {
	  	free(s);
	}	
	free(s);
	return 0;
}
