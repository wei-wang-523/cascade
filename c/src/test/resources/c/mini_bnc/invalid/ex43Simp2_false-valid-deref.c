#include "../../../reserved.h"

/*
   An array with constant-time reset.
*/

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
