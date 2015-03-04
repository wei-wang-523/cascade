typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int * main (int x, int y){
	
	int * a;
	int i = 0;
	
	if ( x< 0 || y < 0 || y > x ) return (int *) 0;
	
	a = (int *) malloc( x * sizeof(int));
	
	if (a == (int *) 0 ) exit(1);
  
  a[i] = 0;
	
	return a;
}