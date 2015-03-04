int main(){
  int a[1000];
  int y, sum = 0;
  for (y=0; y < 100; ++y) {
    for (int i = 0; i < y; ++i) {
      ASSERT(i >= 0 && i <=y);
      sum += i;
    }
  }
  return 1;
}