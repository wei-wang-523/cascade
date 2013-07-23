int main(int *p) {
  int i = 2;
  *(p+i) = 0;
  return *(p+i);
}
