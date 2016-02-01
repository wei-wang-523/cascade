typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int main()
{
  int B[3][2] = {0, 1};
  int *p = B;
  int *q = B[0];
  int *k = &B;
  int *m = &B[0];
  p[1] = 2;
  B[0][1] = 3;
  *(1 + *(B+1)) = 4;
  
  int* C[10];
  C[0] = (int*) malloc(sizeof(int));
  C[1] = (int*) malloc(sizeof(int));
  *(C[0]) = 2;
  
  return 1;
}