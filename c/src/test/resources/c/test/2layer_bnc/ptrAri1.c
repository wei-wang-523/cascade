struct S {
  int a[3];
  int b;
};
 
void foo() 
{
  struct S u;
  u.b = 3;
  int i, k = 0;
  if(k==0) {
    i = 3;
  } else {
    i = 2;
  }
  *(u.a+k) = 2;
  ASSERT(u.b == 2);
}
