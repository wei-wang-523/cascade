typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int main() {
	int **p, *q, *s;
	p = (int **)malloc(2*sizeof(int*));
	q = (int *)malloc(3*sizeof(int));
	if(p != (void *) 0 && q != (void*) 0) {
		p[0] = q;
	}
	s = (int *)malloc(5*sizeof(int));
	p[1] = s;
	free(s);
  free(q);
  free(p);
	return p[0][1];
}
