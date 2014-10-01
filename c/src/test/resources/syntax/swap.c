void swap(int* x, int* y) {
  *x = *x + *y;
  *y = *x - *y;
  *x = *x - *y;
}

void driver(int*a, int*b) {
  int old_a = *a;
  int old_b = *b;
  swap(a,b);
  return;
}