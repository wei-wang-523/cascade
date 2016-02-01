typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

typedef struct foo{
   
   int x;
   int* z;

} foo_t;


int main(int flag){
	foo_t * a, *b;
	
	if(flag > 0) {
		a = (foo_t*)malloc(sizeof(foo_t));
	} else {
		a = (foo_t*)malloc(sizeof(foo_t));
		b = (foo_t*)malloc(sizeof(foo_t));
		a->x = 1;
		free(a);
		a = (foo_t*)malloc(sizeof(foo_t));
		a->x = 0;
	}
  
	{
		a->z = (int*)malloc(sizeof(int) * 5);
    free(a);
	}
	
	{
		free(a->z);
	}
	return 1;
}
