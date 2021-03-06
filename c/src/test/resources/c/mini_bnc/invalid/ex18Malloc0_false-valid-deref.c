typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern int __VERIFIER_nondet_int();

int main(){
  
  int * a;
  int i,j;
  int k = __VERIFIER_nondet_int();
  
  if ( k < 1 ) k = 1;
  
  a= malloc( k * sizeof(int));
  
  ASSUME(k >= 100);
  
  for (i =0 ; i != k; i++) {
    if (a[i] <= 1)
      break;
  }
  i--;
  
  free(a);
  return 0;
  
}