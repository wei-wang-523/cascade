int main() {
	int sum = 0;
	
	for (int i = 0; i<10; i++) {
		sum = sum + i;
	}
	ASSERT(sum == 45);
	return sum;
}
