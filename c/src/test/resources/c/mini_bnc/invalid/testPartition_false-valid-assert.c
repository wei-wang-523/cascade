#include "../../../reserved.h"

int main() {
	int *a, *b, c, d;
	a = b;
	b = &d;
	a = &c;
	a = (int *)&b;
	ASSERT(*a == *b);
	return 0;
}
