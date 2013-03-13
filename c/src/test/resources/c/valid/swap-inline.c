void swap(int*x, int*y) {
  int old_x = *x;
  int old_y = *y;
  *x = *x + *y;
  *y = *x - *y;
  *x = *x - *y;
}
