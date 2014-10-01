int a[1000];

int foo(int x){

  if (x == 0)
    return 1;
  else
    return 0;
}

int main(){
  int y;
  int z;
  for (y=0; y < 100; ++y)
    foo(y);
  
  for (z=0; z < 1000; ++z)
    foo(z);
  
  return 1;
  
}

// test multi-run in a single loop