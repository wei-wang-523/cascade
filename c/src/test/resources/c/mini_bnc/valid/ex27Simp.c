int check(int * x){
  if (!x)
    return 0;
  return 10;
}

int copy(int * a, int * b){
  *a = *b;
  return 2;
}

int foo(int * a, int * b, int n){
  int i;
  if (n <= 0) return 0; // return
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
  
  foo(a,b,5);
  return 2;
}

// Loc 14: bug fixed for null return statement