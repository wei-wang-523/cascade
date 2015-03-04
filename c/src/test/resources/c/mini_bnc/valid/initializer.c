typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

typedef struct _point
{
    int x;
    int y[3];
} Point;

int C[2];
int a = 3;

int main() {
  int B[3][2] = {{1}, 1,  0, {0, 1}};
  Point p = {1, {2,1,3}};
  int A[6];
  char *c = "abc";
  char *d = (char*) malloc(sizeof(char)*4);
  B[0][1] = A[0] + A[1];
  ASSERT(B[0][1] == A[0] + A[1]);
  free(d);
  return B[0][1];
}