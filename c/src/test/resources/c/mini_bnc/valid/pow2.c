#include "../../../reserved.h"

int pow2(int x) {
  return x*x;
}
   
int main() {
  int a, b, result;
  a = 2;
  b = 3;
  result = pow2(a) + pow2(b);
  ASSERT(result == 13);
  return result;
}
