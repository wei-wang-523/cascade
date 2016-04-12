#include "../../../reserved.h"

typedef struct foo{
   
   int x;
   int* z;

} foo_t;


int main() {
	foo_t * a;
	a = (foo_t*)malloc(sizeof(foo_t));
	a = (foo_t*)malloc(sizeof(foo_t));
  int b = 0;
	a->z = &b;
  free(a);
	return 1;
}

// this benchmark is used to check the elements in equivalent class built by union-find 
// (in both steensgaard and fs-steensgaard algorithms) are keep the add-in order