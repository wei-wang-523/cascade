#include "../../reserved.h"

int addInt(int n, int m) {
  return n + m;
}

int minusInt(int n, int m) {
  return n - m;
}

int main() {
  int (*functionPtr)(int, int);
  functionPtr = &addInt;
  int sum = (*functionPtr)(2, 3);
	functionPtr = &minusInt;
  int sum2 = functionPtr(3, 4);
  ASSERT (sum == 5);
	ASSERT (sum2 == -1);
  return 0;
}
