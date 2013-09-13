void foo()
{
  int s1, s2, s3;
  int *p, *q;
  p = &s1;
  p = &s2;
  q = &s3;
  q = p;
}
