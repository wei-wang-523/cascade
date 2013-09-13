void foo() 
{
  int a;
  int *p = &a;
  a = 2;
  *p = 3;
  ASSERT(a == 3);
}
