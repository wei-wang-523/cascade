int main() {
	int *a, *b;
	char d;
	a = (int *) 0;
	b = (int *) &d;
	ASSERT(*b == d);
	return *b;
}

// Invalid. Simple memory model return valid without byte-based reasoning.
// d = 0x01, b = 0xFF01; *b != d.
// Burstall returns invalid at checking assertion "*b == d"
// With type casting between (char*) and (int*) in the statement
// "b := (int *)&d", check the assertion will look at (int*) to get the
// value of b (= &d), and then check (int) to get the value of *b (= d).
// But the value of *b (= d) is stored in (char) array.