struct S {
  int a[3];
  int b;
};
 
void foo() 
{
  struct S u;
  u.b = 3;
  int v[3];
  v[2] = 2;
  int *p = &v[2];
  int *q = &(*p);
  *(v+2) = 2;
  *(u.a+3) = 2;
  ASSERT(u.b == 3);
}
