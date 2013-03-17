int b;

int main(){
   int i,n,j;
   int a[1025];
   int nondet;
   if(nondet) { // if (__NONDET__()){
      n=0;
   } else {
      n=1023;
   }

   i=0;

   while ( i <= n){
      i++;
      j= j +2;
   }

   a[i]=0;
   a[j]=0;
   a[b]=0;
   if (b >= 0 && b < 1023)
      a[b]=1;
   else
      a[b%1023] =1;
   
   return 1;
  
}

// --mem-cell-size 11
// Loc 6, Loc 7 -- declare int k to simulate __NONDET__() 
