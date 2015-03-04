int main() {
	char* d = (char*) malloc (sizeof(char));
	char *s = (char*) malloc (sizeof(char));
	d[0] = '\0';
	s[0] = '\0';
	if((*d++ = *s++) == '\0') {
		int i = 0;
	} else {
		int j = 0;
	}
	
	free(--d);
	free(--s);
  return 0;
}