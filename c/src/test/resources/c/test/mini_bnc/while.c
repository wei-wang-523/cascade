int main() {
	int sum = 0;
	int i = 0;
	while(i<2) {
		sum = sum + i;
		i++;
	}
	while (i<4) {
		sum = sum + i;
		i++;
	}
	ASSERT(sum == 6);
	return sum;
}
