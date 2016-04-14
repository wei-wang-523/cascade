#include "../../../reserved.h"

int main() {
  int * p, a;
  p = (int *)malloc(2*sizeof(int));
  a = p[1];
  free(p);
  return p[1];
}
