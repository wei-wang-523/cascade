//#include "stdlib.h"

int main(int i, int *s) {	
	if(i > 0 ) {
		s = (int *)malloc(5*sizeof(int));
		s[1] = 2;
	} else {
		ASSUME(allocated(s, 5*sizeof(int)));
		s[0] = 1;
		free(s);
//		ASSUME(allocated(s, 5*sizeof(int)));
//		s[1] = 2;
	}
	free(s);
	return 0;
}
