

int main(){
	int x,y;
	int a[10];
	x=1U;
	while (x <= 10U){
		y=10-x;
		ASSERT(valid(&a[y]));
		a[y] = -1;
		x++;
	}
	
	return 1;
	
}