extern int __VERIFIER_nondet_int();

int main(){

   int * a;
   int i,j;
   int k = __VERIFIER_nondet_int();

   if ( k <= 0 ) 
     return -1;
   a= malloc( k * sizeof(int));

   ASSUME(a);
   ASSUME(k >= 100);
   
   for (i =0 ; i != k; i++)
      if (a[i] <= 1) 
    	  break;
   i--;
   
   for (j = 0; j < i; ++j)
      a[j] = a[i];
   

   return 0;

}
