#include "../../../reserved.h"

int main(){
	int a, q, *p;
	p = &a;
	q = *p;
	ASSERT(q==*p);
	return q;
}
