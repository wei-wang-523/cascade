#include "../../../reserved.h"

void f() {
  int fa = 1;
  int fb = 1;
  
  for(int i=0; i < fa; i++) {
    ASSERT(fb == 2);
    fb = 2;
  }
}

void g() {
  int ga = 1;
  int gb = 2;
  
  for(int j=0; j < ga; j++) {
    ASSERT(gb == 2);
    f();
  }
}

int main() {
  int x = 1;
  int y;
  
  for(int k=0; k < x; k++) {
    ASSERT(x==1);
    g();
  }
  
  return 0;
}