
typedef struct {
	int a;
	int b;
} f_t;

int bar(f_t * w, int n){
	ASSERT(valid(w));
	int i;
	for (i=0; i < n ; ++i){
		ASSERT(valid(&(w[i].a)) && valid(&(w[i].b)));
		w[i].a=-1;
		w[i].b=-2;
	}
	return 1;
}

int foo(int * y, int n){
	ASSERT(valid(y));
	int i;
	for (i=0; i < n ; ++i){
		ASSERT(valid(&y[i]));
		y[i]=-1;
	}
	return 1;
}

int main(){
	
	f_t * x, *z;
	int * y, *w; 
	int n; 
	n = __NONDET__();
	ASSUME(n > 0 );
	ASSUME( n < 100);
	x = (f_t*) malloc(n * sizeof(f_t));
	y = (int *) x;
	foo(y,2*n);
	w = (int *) malloc( 2*n * sizeof(int));
	z = (f_t*) w;
	
	bar(z,n);
	
	return 1;
}