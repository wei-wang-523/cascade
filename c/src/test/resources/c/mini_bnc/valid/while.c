#include "../../../reserved.h"

int main() {
	int sum = 0;
	int i = 0;
	while(i<5) {
		sum = sum + i;
		i++;
	}
	while (i<10) {
		sum = sum + i;
		i++;
	}
	ASSERT(sum == 45);
	return sum;
}
