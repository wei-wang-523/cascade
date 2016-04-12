#include "../../../reserved.h"

int main() {
	int a[1024];
	a[0] = 4096;
	ASSERT(a[0] == 4096);
	return 0;
}
