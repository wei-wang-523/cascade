int main() {
	char* d = (char*) malloc (sizeof(char));
	char *s = (char*) malloc (sizeof(char));
	d[0] = '\0';
	s[0] = '\0';
	
	do {
		int i = 1;
		if(i > 1) break;
	} while ((*d++ = *s++) == '\0');
	
	free(--d);
	free(--s);
  return 0;
}