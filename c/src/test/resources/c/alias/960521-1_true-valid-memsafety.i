int *a, *b;
int n;
void foo ()
{
  int i;
  for (i = 0; i < n; i++)
    a[i] = -1;
  for (i = 0; i < 32768 - 1; i++)
    b[i] = -1;
}
int main ()
{
  n = 32768;
  a = malloc (n * sizeof(*a));
  b = malloc (n * sizeof(*b));
  *b++ = 0;
  foo ();
  if (b[-1])
  { free(a); free(b); }
  else
  { free(a); free(b-1); }
  return 0;
}
