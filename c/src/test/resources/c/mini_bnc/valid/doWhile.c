#include "../../../reserved.h"

int main() {
	int sum = 0;
	int i = 0;
	do {
		sum = sum + i;
		i++;
  } while(i<5);
	
  do {
		sum = sum + i;
		i++;
  } while (i<10);
  
	ASSERT(sum == 45);
	return sum;
}
