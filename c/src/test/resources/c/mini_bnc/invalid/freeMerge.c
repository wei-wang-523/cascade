//#include "stdlib.h"

int main(int i, int *s) {
	s = (int *)malloc(5*sizeof(int));
	if(i <= 0 ) {
	  	free(s);
	}	
	free(s);
	return 0;
}
