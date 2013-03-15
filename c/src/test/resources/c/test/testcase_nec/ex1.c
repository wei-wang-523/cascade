#define N 20 // (1<<10)
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
  return q[-1] ; 
}

// LOC1: --mem-cell-size 11
// LOC1: for loop unrolling, change N from 1<<10 as 20; otherwise, got error java.lang.OutOfMemoryError: Java heap space.
