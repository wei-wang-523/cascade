typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int * a;


int test(int * n ){
  
  int i;
  
  for (i = 0; i < (*n); ++i){
    a[i] = 0;
  }
  
  return 1;
}


int main(){
  
  int n = 9;
  
  if (n <= 0 || n >= 1024){
    exit(1);
  } else {
    a = (int *) malloc( n * sizeof(int));
  }
  
  test(&n);
  
  return 1;
}