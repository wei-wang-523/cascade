typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int main() {
  int * p, a;
  p = (int *)malloc(2*sizeof(int));
  a = p[1];
  free(p);
  return p[1];
}
