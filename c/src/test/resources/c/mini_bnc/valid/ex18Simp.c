
int main(){

   int * a;
   int i,j;
   int k = __NONDET__();

   if ( k <= 0 ) 
     return -1;
   a= malloc( k * sizeof(int));

   ASSUME(a);
   ASSUME(k >= 100);
   
   for (i =0 ; i != k; i++)
      if (a[i] <= 1) 
    	  break;
   i--;  

   return 0;

}
