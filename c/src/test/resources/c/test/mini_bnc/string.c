int main() {
  char * s = "123";
  s[0] = '\u0000';
  return s[1];
}
