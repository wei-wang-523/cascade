typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern int __VERIFIER_nondet_int();

int * a;
int n;

int test(){
	
  int i;
  
  for (i = 0; i < n; ++i) {
    a[i] = 0;		
  }
  
  return 0;
}


int main(){
	
  n = __VERIFIER_nondet_int();
	
  if (n <= 0 || n >= 1024){
    n=5;
    a = (int *) malloc(n * sizeof(int)); // region
  } else {
    a = (int *) malloc(n * sizeof(int)); // region_0
  }
  
  test();
  free(a);
  return 1;
}

// Non-lambda encoding with order Flat and Burstall mode gets invalid. The 
// assumption valid_malloc(a, n) of region_0, is ignored at phi-node, when
// (n <= 0 || n >= 1024). But the last region is set as the region_0, though 
// region_0 is not really allocated. Reasoning about disjointness of memory
// in order mode, only ensures all the stack variables' addresses are larger 
// than the last region -- region_0. But the disjoint(region, region_0), 
// which was specified at the valid_malloc(a, n) of region_0, is ignored at 
// phi-node. Thus, the disjointess of all the stack variables' addresses and 
// region are not in the memory disjointness. Therefore, region may be 
// addr_of_n or addr_of_a.
