int main(){
	int *p;
	char *q = (char*)malloc(sizeof(char));
	*q = 'a';
	p = (int *)q;
	ASSERT( *p == 'a');
	return (int) *p;
}
