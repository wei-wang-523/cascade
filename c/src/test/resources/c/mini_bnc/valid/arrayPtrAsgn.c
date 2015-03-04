int main()
{
  int C[6];
  int *p = &C;
  int i = 5;
  C[i] = 3;
  p[i] = 4;
  return 1;
}