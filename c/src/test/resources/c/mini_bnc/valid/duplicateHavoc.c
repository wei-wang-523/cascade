int main() {
	int sum = 0;
	
	for (int i = 0; i<=10; i++) {
		sum = sum;
		sum = sum + i;
	}
	ASSERT(sum == 55);
	return sum;
}
