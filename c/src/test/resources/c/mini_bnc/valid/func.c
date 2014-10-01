int returnOne();
int addOne(int x, int y);


int main() {
  int x = 1;
  int y;
  
  y = addOne(1, returnOne());
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