#include "../../reserved.h"

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
  // steens-cfs treats unallocated 'b->dataWriteEvidence[0]' and 
  // 'b->dataWriteEvidence[1]' as Bottom ECR and thus won't merge
  // them; if have 
  //  'b->dataWriteEvidence = (idx_t *)malloc(sizeof(idx_t) * n)'
  // then they will be merged.
  b->dataWriteEvidence[0] = 0;
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