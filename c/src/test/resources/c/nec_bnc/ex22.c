int check(int * x){
  if (!x) // return 0;
    return 0;
  
  return 10;
}

int copy(int * a, int * b){
   *a = *b;
   return 2;
}

int foo(int * a, int * b, int n){
   int i;
   if (n <= 0) return 1; // return;
   if (!check(a))
      return 1;

   if (!check(b))
      return 1;

   for (i=0; i < n; ++i){
      copy(a+i,b+i);
   }

   copy(a+n,b+n);
   return 1;
}

#define NULL (int *) 0
int main(){
   int a[100],b[200];

   foo(NULL,a,100);
   foo(a,NULL,200);
   foo(a,b,50);
   foo(a,b,20);
   return 2;
}

// LOC 3: put "return 0" in the next line. 
// LOC 15: code bug return; add it as return 1.

// ex22-inv cause inconsisitent result of Burstall and Partition memory models.
// In copy(...) function, *a(@copy) is updated, and thus *a(@copy) is havoced
// before going into the for-loop in foo(...), *a(@copy) might be assigned the
// a to *a, and thus cause failure in checking valid(a + i)