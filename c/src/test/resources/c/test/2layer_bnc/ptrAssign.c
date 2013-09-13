typedef struct account{
	int x;
	int y;
} acc;

acc r;

int foo(int * ptr){
	if (ptr == &(r.x))
		*ptr = 0;
	if (ptr == &(r.y))
		*ptr = 1;

	return 1;
}


int main(){

	foo (&(r.x));
	foo( &(r.y));

	ASSERT(r.x <= r.y);
	return 1;
}
