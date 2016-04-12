#include "../../../reserved.h"

int main() {
	char* d = (char*) malloc (sizeof(char));
	char *s = (char*) malloc (sizeof(char));
	d[0] = '\0';
	s[0] = '\0';
	
	int i = 0;
	
	switch ((*d++ = *s++)) {
		case '\0':
			i++;
			break;
		case 'a':
			i+=2;
		default:
			i--;
			break;
	}
	
	free(--d);
	free(--s);
  return 0;
}