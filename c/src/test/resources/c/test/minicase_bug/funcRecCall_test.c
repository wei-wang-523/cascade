int addOne(int x) {
  x=x+1;
  x = addOne(x);
  return x;
}

int main() {
  int x = 1;
  x = addOne(x);
  return x;
}
