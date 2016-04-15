#include "../../../reserved.h"

typedef struct foo{
   
   int x;
   int* z;

} foo_t;


int main(){
  int* p;
	
  foo_t *a = (foo_t*)malloc(sizeof(foo_t));
  
	{
    a->z = NULL;
    free(a);
	}
  return 1;
}
