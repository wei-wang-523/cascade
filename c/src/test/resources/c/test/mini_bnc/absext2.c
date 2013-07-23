int abs(int x) {
  int result;
  if(x>=0)
    result = x;
  else
    result = -x;
  return result;
}
   
int main() {
  int a, result;
  a = -4;
  result = abs(a) - abs(-a);
  return result;
}
