int main() {
  int a = 0;
  int b;
  b = (++a) + (a--);
  b--;
  ASSERT(a == 0 && b == 2);
  return a;
}
