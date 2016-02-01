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
	
  n = __NONDET__();
	
  if (n <= 0 || n >= 1024){
    n=5;
    a = (int *) malloc(n * sizeof(int)); // region
  } else {
    a = (int *) malloc(n * sizeof(int)); // region_0
  }
  ASSUME(a != (int *) 0);
  
  
  test();
  
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
