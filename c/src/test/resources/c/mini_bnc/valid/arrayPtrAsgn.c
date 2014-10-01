int main()
{
  int C[6];
  int *p = &C;
  int i = 5;
  ASSERT(valid(&C[i]));
  ASSERT(valid(&p[i]));
  return 1;
}