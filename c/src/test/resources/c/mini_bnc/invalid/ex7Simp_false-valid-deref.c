typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int * main (int x){
	
	int * a;
  
  if (x < 1) x = 1;
  
	a = (int *) malloc( x * sizeof(int));
	
  for(int i = 0; i < x; i++) {
    a[i] = 1;
  }
  
  free(a);
	return a;
	
}

// test forall formula in assertion with valid predicate.
// design for lambda encoding, to test if both z3 and cvc4
// can handle quantified formula parsed via CExpressionEncoder properly