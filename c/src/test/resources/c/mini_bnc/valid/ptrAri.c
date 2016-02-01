int main(int *p) {
  p = (int*)malloc(sizeof(int)*3);
  int i = 2;
  *(p+i) = 0;
  return *(p+i);
}
