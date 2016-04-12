#include "../../../reserved.h"

int main() {
	int sum = 0;
	
	for (int i = 0; i<=3; i++) {
		sum = sum;
		sum = sum + i;
	}
	ASSERT(sum == 6);
	return sum;
}

// duplicate havoc is not been tested in non-ctrl version, we're not support havoc