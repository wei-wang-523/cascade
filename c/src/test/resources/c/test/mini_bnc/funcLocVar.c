int addTen(int y);

int main() {
  int x = 1;
  int y;
  
  y = addTen(x);
  ASSERT(y == x+10);
  y = addTen(y);
  ASSERT(y == x+20);
  return y;
}

int addTen(int a) {
	int x;
	ASSERT(x != 10);
	x = 10;
	return a + x;
}