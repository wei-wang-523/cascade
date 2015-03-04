int main() {
	char* d = (char*) malloc (sizeof(char));
	char *s = (char*) malloc (sizeof(char));
	d[0] = '\0';
	s[0] = '\0';
	char c[] = {(*d++ = *s++), 'D'};
	free(--d);
	free(--s);
  return 0;
}