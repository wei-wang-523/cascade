int main() {
  const char * s = "123";
  s[0] = '2';
  ASSERT(s[3] == '\u0000');
  return s[1];
}
