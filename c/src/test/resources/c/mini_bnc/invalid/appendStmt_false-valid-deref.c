int main() {
  char* d1 = (char*) malloc (sizeof(char));
  char* s1 = (char*) malloc (sizeof(char));
	char* d = d1;
	char* s = s1;
	d[0] = '\0';
	s[0] = '\0';
	while(1) {
		if((*d++ = *s++) == '\0')
			d[0] = 'a'; break;
	}
	free(d1);
	free(s1);
  return 0;
}