#include "../../../reserved.h"

int abs(int x) {
  if(x>=0) {
  	int i = 0;
    return x;
  } else {
  	int i = -1;
    return -x;
  }
}
  
int main() {
  int a, abs_a;
  abs_a = abs(a);
  ASSERT(abs_a >= 0);
  return abs_a;
}
