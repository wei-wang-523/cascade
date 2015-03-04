int abs(int x) {
  if(x>=0)
    return x;
  else
    return -x;
}
   
int main() {
  int a, result;

  result = abs(a) - abs(-a);
  ASSERT(result != 0);
  return result;
}
