int abs(int x) {
  int result;
  if(x>=0)
    result = x;
  else
    result = -x;
  return result;
}
  
int main() {
  int a, abs_a;
  a = -4;
  abs_a = abs(a);
  return abs_a;
}
