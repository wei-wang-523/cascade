void swap(int*x, int*y) { int old_x, old_y;
  old_x = *x;
  old_y = *y;
  *x = *x + *y;
  *y = *x - *y;
  *x = *x - *y;
}
