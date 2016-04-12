#include "../../../reserved.h"

typedef struct foo{
   
   int x;
   int* z;

} foo_t;


int main(int flag){
	foo_t * a, *b;
  int* p;
	
	if(flag > 0) {
		a = (foo_t*)malloc(sizeof(foo_t));
	} else {
		a = (foo_t*)malloc(sizeof(foo_t));
		b = (foo_t*)malloc(sizeof(foo_t));
		a->x = 1;
		free(a);
		a = (foo_t*)malloc(sizeof(foo_t));
		a->x = 0;
	}
  
	{
		a->z = (int*)malloc(sizeof(int) * 5);
    p = a->z;
    free(a);
	}
	
	{
		free(p);
	}
	return 1;
}
