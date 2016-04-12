#include "../../../reserved.h"

int main (){
	int * a = (int *) calloc(2, sizeof(int));
	a[0] = 1;
	ASSERT(a[1] == 0);
	ASSERT(a[0] == 1);
  free(a);
	return 0;
}