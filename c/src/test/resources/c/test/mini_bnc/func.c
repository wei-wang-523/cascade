int returnOne();
int addOne(int x, int y);
int foo(int x);
int bar(int x);
int main() {
  int x = 1;
  int y = foo(x);
  bar(x);
  y = addOne(x, returnOne());
  ASSERT(y == x+1);
  return y;
}

int returnOne() {
	return 1;
}

int addOne(int x, int y) {
	x=x+y;
	return x;
}