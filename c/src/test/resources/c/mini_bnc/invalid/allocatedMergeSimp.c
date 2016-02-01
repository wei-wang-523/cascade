typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

typedef struct foo{
   int x;
   int* z;
} foo_t;

int main(int flag){
	foo_t * a;
	
	if(flag > 0) {
		a = (foo_t*)malloc(sizeof(foo_t));
		a->x = 1;
	}
	ASSERT(implies(flag > 0, a->x == 1));
	
	free(a);
	return 1;
}

// test resolve phi-node, should includes all the partitions, not the common ones.