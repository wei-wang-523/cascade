int N = 10;

int addOne(int k){
	return k+1;
}

int returnOne(){
	return 1;
}

int main(int a, int b, int c){
	int flag1,flag2;
	
	if (a > b) {
		int y1 = 1;
	} else {
		int y2 = 0;
	}
	
	for (int i = 0; i < 10; i++) {
		int y3 = 2;
	}
	
	if (b > c){
		int y4 = 1;
	} else {
		int y5 = 0;
	}
	
	for (int i = 0; i < 10; i++) {
		int y6 = 1;
	}
	
	if (flag1 == 1){
		if (flag2 == 1){
			int y7 = 3;
		}
	}
	
	int j = 0;
	
	while (j<3) {
		int y8 = 0;
		j++;
	}
	
	if ( flag2 -flag1 <= 0 ) {
		if (flag1 + flag2 < 1){
			int y9 = 4;
		}
	}
	return 1;
}