typedef int size_t;
typedef int data_t;
typedef size_t idx_t;
int __NONDET__();

typedef struct {
  data_t resetVal;
  data_t *data;
  idx_t numData;
  idx_t maxNumData;
  idx_t *dataIdx;
  idx_t *dataWriteEvidence;
} buf_t;

int main() {
  buf_t **bufs = (buf_t **)malloc(1 * sizeof(buf_t *));
	
	buf_t *b = (buf_t *)malloc(sizeof(buf_t));
	
  b->data = (data_t *)malloc(sizeof(data_t));
  b->maxNumData = 1;
	b->numData = 0;
  b->dataWriteEvidence = (idx_t *)malloc(sizeof(idx_t));
	ASSERT(valid(&b->dataWriteEvidence[0]));
	b->dataWriteEvidence[0] = 1;
	
	bufs[0] = b;
	
	idx_t idx = __NONDET__();
  ASSUME(0 <= idx && idx < bufs[0]->maxNumData);
	
	idx_t writeDataTo = bufs[0]->dataWriteEvidence[idx];
	
	ASSERT(bufs[0]->numData < bufs[0]->maxNumData);
	bufs[0]->dataWriteEvidence[idx] = bufs[0]->numData;
	
  return 1;
}

// test steensgaard pointer analysis to getPointsToVar
// lambda-based encoding gets stuck at assume statement (the 3rd one), 
// when evaluate the assumption (substitute old expressions with new expressions,
// z3 gets stuck but cvc4 works well 