//#include "stdlib.h"

int main() {
	int **p, *q, *s;
	p = (int **)malloc(2*sizeof(int*));
	q = (int *)malloc(3*sizeof(int));
	if(p != 0 && q != 0) {
		p[0] = q;
	}
	s = (int *)malloc(5*sizeof(int));
	p[1] = s;
	free(s);
	return p[0][1];
}
