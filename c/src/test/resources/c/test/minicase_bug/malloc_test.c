//#include "stdlib.h"

int main() {
  int * p;
  p = (int *)malloc(2*sizeof(int));
  p[1] = 1;
  return p[1];
}
