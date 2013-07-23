int returnOne() {
	return 1;
}

int addOne(int x, int y) {
	x=x+y;
	return x;
}

int main() {
  int x = 1;
  int y; 
  y = addOne(x, returnOne());
  return y;
}
