extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
  ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();
void main() {
  int x = 1;
  int y = 0;
  while (y < 1000 && __VERIFIER_nondet_int()) {
    x = x + y;
    y = y + 1;
  }
  
  int z = y < 1000 ? x : y;
  
  __VERIFIER_assert(x >= y);
}