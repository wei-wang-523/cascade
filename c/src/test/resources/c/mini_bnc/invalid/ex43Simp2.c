typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;


/*
   An array with constant-time reset.
*/

typedef int data_t;
typedef size_t idx_t;
typedef int bool_t;
#define NULL (int *) 0
int __NONDET__();
int ASSUME(int);
int ASSERT(int);

typedef struct {
  data_t resetVal;
  data_t *data;
  idx_t numData;
  idx_t maxNumData;
  idx_t *dataIdx;
  idx_t *dataWriteEvidence;
} buf_t;

int main() {

  int i,j;
  buf_t **bufs = (buf_t **)malloc(3 * sizeof(buf_t *));
  
  for (i=0; i<1; i++) {
    buf_t *b = (buf_t *)malloc(sizeof(buf_t));
    b->data = (data_t *)malloc(sizeof(data_t) * 3);
    
    for (j=0; j<3; j++) {
      b->dataWriteEvidence[j] = 3;
    }
    
    bufs[i] = b;
  }
  
  idx_t writeDataTo = bufs[0]->dataWriteEvidence[1];

  return 1;
}

// created for testing path-based encoding
