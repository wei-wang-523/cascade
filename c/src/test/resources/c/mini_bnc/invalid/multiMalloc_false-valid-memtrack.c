typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

typedef struct foo{
   
   int x;
   int* z;

} foo_t;


int main() {
	foo_t * a;
	a = (foo_t*)malloc(sizeof(foo_t));
	a = (foo_t*)malloc(sizeof(foo_t));
  int b = 0;
	a->z = &b;
  free(a);
	return 1;
}

// this benchmark is used to check the elements in equivalent class built by union-find 
// (in both steensgaard and fs-steensgaard algorithms) are keep the add-in order