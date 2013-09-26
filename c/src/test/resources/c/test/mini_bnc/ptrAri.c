int main(int *p) {
  int i = 2;
  int a = 4;
  *(p+i) = 0;
  return *(p+i);
}
