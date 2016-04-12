#include "../../../reserved.h"

int main() {
  unsigned long i = (unsigned long) sizeof(int);
  ASSERT(i==4);
  return i;
}
