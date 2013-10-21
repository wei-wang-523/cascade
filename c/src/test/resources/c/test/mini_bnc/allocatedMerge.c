//#include <stdlib.h>
typedef struct foo{
   
   int x;
   int* z;

} foo_t;


int main(int flag){
	foo_t * a, *b;
	
	if(flag > 0) {
		a = (foo_t*)malloc(sizeof(foo_t));
	} else {
		ASSUME(allocated(a, sizeof(foo_t)) && allocated(b, sizeof(foo_t)));
		a->x = 1;
		free(a);
		ASSUME(allocated(a, sizeof(foo_t)));
		a->x = 0;
	}
	ASSUME(a);
//	free(a);
	ASSERT(valid(&(a->z)));
	{ 
		a->z = (int*)malloc(sizeof(int) * 5);
		//	ASSUME(a->z);
		ASSERT(valid(a->z));
	}
	
	{
		free(a);
	}
	return 1;
}
