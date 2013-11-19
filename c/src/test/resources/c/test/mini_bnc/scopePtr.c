int N = 10;

int addOne(int k){
	return k+1;
}

int returnOne(){
	return 1;
}

int main(int a, int* b, int* c){
	int flag1,flag2;
	
	if (a > *b) {
		int *y1 = (int *)malloc(sizeof(int));
		y1 = &a;
	} else {
		int *y2 = (int *)malloc(sizeof(int));
		y2 = &a;
	}
	
	for (int i = 0; i < 10; i++) {
		int *y3 = (int *)malloc(sizeof(int));
		y3 = &a;
	}
	
	if (b > c){
		int *y4 = (int *)malloc(sizeof(int));
		y4 = &a;
	} else {
		int *y5 = (int *)malloc(sizeof(int));
		y5 = &a;
	}
	
	for (int i = 0; i < 10; i++) {
		int *y6 = (int *)malloc(sizeof(int));
		y6 = &a;
	}
	
	if (flag1 == 1){
		if (flag2 == 1){
			int *y7 = (int *)malloc(sizeof(int));
			y7 = &a;
		}
	}
	
	int j = 0;
	
	while (j<3) {
		int *y8 = (int *)malloc(sizeof(int));
		y8 = &a;
		j++;
	}
	
	if ( flag2 -flag1 <= 0 ) {
		if (flag1 + flag2 < 1){
			int *y9 = (int *)malloc(sizeof(int));
			y9 = &a;
		}
	}
	ASSERT(1==0);
	return 1;
}