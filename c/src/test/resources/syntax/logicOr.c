extern void __VERIFIER_error(void);

int main() {
  int a = 1;
  int c = a == 1 ? (a = 1) : (a = 0);
  if (a) { ERROR: __VERIFIER_error(); return 1; }
  return 0;
}