int main() {
  char s[] = "123";
  int a;
  s[0] = '2';
  a = 1;
  ASSERT(s[3] == '\u0000');
  return s[1];
}
