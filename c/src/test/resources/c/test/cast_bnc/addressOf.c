void foo() 
{
  int a;
  char *p = (char*) &a;
  a = 2;
  *p = 3;
  ASSERT(a == 3);
}
