int main(int *p, char *q){
	int *p = (int *)malloc(sizeof(int));
	char *q = (char*)malloc(sizeof(char));
	*q = 'a';
	p = (int*)q;
	*p = 'b';
	ASSERT( *q == 'a');
	return (int) *p;
}
