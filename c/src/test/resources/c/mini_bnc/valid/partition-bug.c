#include "../../../reserved.h"

int main() {
	int *a = (int *)malloc(sizeof(int) * 12);
	int *b = (int *)malloc(sizeof(int) * 25);
	if (a==b) {
		return 0;
	}
	
	free(a);
	free(b);
	return 1;
}