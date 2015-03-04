struct {
  int a[3];
  int b;
} acc;

int main() {
  *(acc.a + 3) = 2;
  ASSERT(acc.b == 2);
}