typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int main(int *p) {
  p = (int*)malloc(sizeof(int)*3);
  int i = 2;
  *(p+i) = 0;
  free(p);
  return 0;
}
