#include "../../../reserved.h"

int main() {
  int a = 1;
  int A[3][3] = {{1,2,3}, {1,0,1}, {0,2,1}};
  A[1][1] = a;
  ASSERT(A[1][1] == 1 && A[2][2] == 1);
  return A[1][1];
}
