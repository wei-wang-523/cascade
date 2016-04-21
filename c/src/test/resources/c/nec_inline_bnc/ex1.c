#define N (1<<10)
int A[N] ;
int B[N/2] ;

int pair ( int *p ) 
{
  return *p + p[1] ;
}


int main() 
{
  int *q ;
  int i , j ; 

  for ( i = 0 , j = 0 , q = B ; i < N/2 ; i++ , j += 2, q++) {
    *q = pair ( &(A[j]) );
  }
  ASSERT(valid(q[-1]));
  return q[-1] ; 
}
