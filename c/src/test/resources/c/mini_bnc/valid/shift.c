#include "../../../reserved.h"

int main() {
	int i = 1 << 3;
	int j = i/2;
	ASSERT(j == 4);
	return j;
}
