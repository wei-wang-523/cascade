
int foo(int x);
int a [100];
int b[200];
void g(int * x, int y){
	x[y]=0;
}


int main(){
	int i,j;
	for(i=0; i < 100; ++i){
		g(a,i);
		g(b,i);
		foo(i);
	}
	ASSERT(forall(idx, implies(0<=idx && idx <100, a[idx] == 0 && b[idx] == 0)));
	for(j=100;j < 200; ++j){
		g(b,j);
		foo(j);
	}
	
    ASSERT(forall(idx_0, implies(100<=idx_0 && idx_0 < 200, b[idx_0] == 0)));
	
	return 1;
}