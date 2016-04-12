#include "../../../reserved.h"

int main() {
	
	int flag;
	int * a;
	
	if (flag){
		a = (int *) malloc(5 * sizeof(int));
	} else {
		a = (int *) malloc(5 * sizeof(int));
	}
	
	a[0] = 1;
  free(a);
	return 1;
}

// The loop invariant will fail with partition memory model, but lambda parition will pass