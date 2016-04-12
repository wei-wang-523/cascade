#include "../../../reserved.h"

int *p, *q, *r;

void g(int** fp) {
	int local;
	p = &local;
}

void f() {
  q = (int*)malloc(sizeof(int));
  g(&q);
  r = (int*)malloc(sizeof(int));
}
  
int main() {
  p = (int*)malloc(sizeof(int));
  f();
  g(&p);
  p = (int*)malloc(sizeof(int));
  
}