int main() {
	int *a, *b, *c, *d;
	a = b;
	b = &d;
	a = &c;
	a = &b;
	ASSERT(*a == *b);
	return 0;
}
