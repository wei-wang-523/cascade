#include "../../../reserved.h"

int main (int x, int y){
	
	int * a;
	int i = 0;
	
	if ( x< 0 || y < 0 || y > x ) return 0;
	
	a = (int *) malloc( x * sizeof(int));
	
	if (a == (int *) 0 ) exit(1);
  
  a[i] = 0;
	
	return 0;
}