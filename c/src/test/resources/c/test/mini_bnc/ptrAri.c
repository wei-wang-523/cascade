int main(int *p) {
	ASSERT(allocated(p, sizeof(int)*3));
  int i = 2;
  *(p+i) = 0;
  return *(p+i);
}
