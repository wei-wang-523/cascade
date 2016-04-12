#include "../../../reserved.h"

int a[1000];

int foo(int x){
  int i;
  if (x == 0) 
    return 1;
  ASSERT(x > 0 && x < 1000);
  
  for (i = 0; i < x; ++i) {
    a[i]=0;
  }
  return 0;
}

int main(){
  int y;
  for (y=0; y < 100; ++y)
    foo(y);

  return 1;
  
}
