int f(int arg) {
  return arg+1;
}

int main() {
  int a, b;
  
  if (f(a) < f(b)) {
    return -1;
  }
  
  return 1;
}