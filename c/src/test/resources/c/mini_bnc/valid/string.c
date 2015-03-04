int main() {
  const char * s = "123";
  s[0] = '2';
	char str[50] = "This is string.h library function";	
	char *str2 = "This is string.h library function";
	ASSERT(str[3] == 's' && str2[3] == 's');
  ASSERT(s[3] == '\u0000');
  return s[1];
}
