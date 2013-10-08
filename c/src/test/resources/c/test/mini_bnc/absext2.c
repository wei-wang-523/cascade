int abs(int x) {
  if(x>=0)
    return x;
  else
    return -x;
}
   
int main() {
  int a, result;
  a = -4;
  result = abs(a) - abs(-a);
  return result;
}
