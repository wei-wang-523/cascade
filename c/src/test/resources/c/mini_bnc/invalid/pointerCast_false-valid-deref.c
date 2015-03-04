typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

typedef struct foo{
  
  int x;
  int z;
  
} foo_t;


int main(int n){
  ASSUME(n > 1);
  foo_t * a, a1;
  int * b;
  a = (foo_t*) malloc(n * sizeof(foo_t));
  
  b = (int *)a; /*-- down casting. Length(b) = 2 * Length(a) --*/
  b[2*n -1 ] = '\0';
  
  free(a);
  return 1;
}