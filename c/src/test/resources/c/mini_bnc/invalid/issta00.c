typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int *p, *q, *r;

void g(int** fp) {
	int local;
	p = &local;
}

void f() {
  q = (int*)malloc(sizeof(int));
  g(&q);
  r = (int*)malloc(sizeof(int));
}
  
int main() {
  p = (int*)malloc(sizeof(int));
  f();
  g(&p);
  p = (int*)malloc(sizeof(int));
}
