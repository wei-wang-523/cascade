int main() {
	int *a, *b, c, d;
	a = &c;
	b = &d;
	*a = 1;
	*b = 2;
	ASSERT(c == 1 && d == 2);
	return *a;
}
