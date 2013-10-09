int abs(int x) {
  if(x>=0)
    return x;
  else
    return -x;
}
  
int main() {
  int a, abs_a;
  abs_a = abs(a);
  ASSERT(abs_a >= 0);
  return abs_a;
}
