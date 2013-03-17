
int foo(int x);
int a[10]; //a[100]
int b[20]; //b[200]

void g(int * x, int y){
   if (x == a)
      x[y]=0;
   else
      x[2*y] = 0;
}


int main(){
   int i,j;
   for(i=0; i < 10; ++i){ // i < 100
     g(a,i); //a[i] = 0
     g(b,i); //b[2i] = 0 
     foo(i); //?
   }

   for(j=10;j < 20; ++j){ // j = 100; j < 200
     g(b,j); //b[2j] = 0
     foo(j); //?
   }

   return 1;
   
}
