int abs(int x) {

  if(x>=0)
    return x;
  else
    return -x;
}

  
int main() {
  int a, abs_a;
  a = -4;
  abs_a = abs(a);
  return abs_a;
}
