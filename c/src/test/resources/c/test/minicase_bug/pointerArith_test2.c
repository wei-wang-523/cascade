struct S {
  int a[3];
  int b;
};
 
void foo() 
{
  struct S u;
  u.b = 3;
  *(u.a+3) = 2;
  //  _(assert u.b == 2)
}
