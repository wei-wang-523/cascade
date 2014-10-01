typedef struct _point
{
    int x;
    int y[3];
} Point;

int C[2];
int a = 3;

int main() {
  int B[3][2] = {{1}, 1, {0, 1}};
  Point p = {1, {2,1,3}};
  int A[6];
  char *c = "abc";
  char *d = (char*) malloc(sizeof(char)*4);
  B[0][1] = A[0] + A[1];
  ASSERT(B[0][1] == A[0] + A[1]);
  return B[0][1];
}