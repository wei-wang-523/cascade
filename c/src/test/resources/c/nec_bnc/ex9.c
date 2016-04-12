#include "../../reserved.h"

int * a;
int n;

int test(){

   int i;

   for (i = 0; i < n; ++i){

      if (a[i])
         n--;
      
      a[i] = 0;
      
      
   }

   return 0;
}


int main(){

   n = __VERIFIER_nondet_int();
   
   if (n <= 0 || n >= 1024){
      n=5;
      a = (int *) malloc(n * sizeof(int));
   } else {
      a = (int *) malloc( n * sizeof(int));
   }
 
   ASSUME(a != NULL);

   test();

   return 1;
}

// LOC26: 1024 is out of the bound of integer with size 8 bytes.
