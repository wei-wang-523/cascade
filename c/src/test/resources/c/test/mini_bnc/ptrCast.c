int main() {
	int *a, *b;
	char d;
	a = (int *) 0;
	b = (int *) &d;
	ASSERT(*b == d);
	return *b;
}
