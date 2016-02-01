int main()
{
  int B[5];
  int *p = B;
  int *q = &B;
  int idx;
  ASSUME(idx >= 0 && idx < 5);
  ASSERT(valid(&B[idx]));
  ASSERT(valid(&p[idx]));
  ASSERT(valid(&q[idx]));
}