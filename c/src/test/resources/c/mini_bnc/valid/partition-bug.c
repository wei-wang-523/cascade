typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void free (void *__ptr) __attribute__ ((__nothrow__ , __leaf__));

int main() {
	int *a = (int *)malloc(sizeof(int) * 12);
	int *b = (int *)malloc(sizeof(int) * 25);
	if (a==b) {
		return 0;
	}
	
	free(a);
	free(b);
	return 1;
}