int main() {
	char* d = (char*) malloc (sizeof(char));
	char *s = (char*) malloc (sizeof(char));
	d[0] = '\0';
	s[0] = '\0';
	
	for (int i = 0; ((*d++ = *s++) != '\0'); i++) {
		if(i > 1) break;
	}
	
	free(--d);
	free(--s);
  return 0;
}