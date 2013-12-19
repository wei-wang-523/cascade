int main(int a, char b){
	int *p = &a;
	char *q = &b;
	p = (int *)q;
	ASSERT( *q == *p);
	return *p;
}
