extern int __VERIFIER_nondet_int();

int addTen(int y);

int main() {
  int x = 1;
  int y;
  
  if (__VERIFIER_nondet_int()) {
	  y = addTen(x);
	  ASSERT(y == x+10);
  } else {
	  y = addTen(x);
	  y = addTen(y);
	  ASSERT(y == x+20);
  }
  return y;
}

int addTen(int a) {
	int x;
	ASSERT(x != 10);
	x = 10;
	return a + x;
}