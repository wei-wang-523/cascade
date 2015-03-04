
typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

/*
   An array with constant-time reset.
*/

typedef int size_t; // redef type size_t as int
typedef int data_t;
typedef size_t idx_t;
typedef int bool_t;
typedef struct {
  data_t resetVal;
  data_t *data;
  idx_t numData;
  idx_t maxNumData;
  idx_t *dataIdx;
  idx_t *dataWriteEvidence;
} buf_t;

buf_t *bufAlloc(size_t n) {
  int i;
  buf_t *b = (buf_t *)malloc(sizeof(buf_t));
//  b->data = (data_t *)malloc(sizeof(data_t) * n);
//  b->maxNumData = n;
//  b->numData = 0;
  b->dataWriteEvidence[0] = 0; // for (i=0; i<n; i++)
  b->dataWriteEvidence[1] = 0;
  return b;
}

int main(int argc, char *argv[]) {
  const int numWrites = 4, numReads = 10, numBufs = 3, maxN = 20;
  int i,j;
  data_t datum;
  bool_t shouldReset;
  bool_t datumOut;
  
  buf_t **bufs = (buf_t **)malloc(numBufs * sizeof(buf_t *));
  for (i=0; i<numBufs; i++)
    bufs[i] = bufAlloc(maxN);

  return 1;
}