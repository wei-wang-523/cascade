
int main(int i, int j){
	ASSUME(i < 0);
	int x,y;
	int a[1];
	x=i;
	y=j;
	
	while (x!=0) {
		x--;
		y--;
	}
	
	if (i==j){
		ASSERT( y == 0);
		
		
	}
	
	
	return 1;
}
