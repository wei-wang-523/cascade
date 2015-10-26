struct A18 {
  int data;
};

void *ldv_malloc(int size) {
  if(__VERIFIER_nondet_int()) {
    return malloc(size);
  } else {
    return 0;
  }
};


void entry_point(void) {
  int len = 10;
  struct A18 **array = (struct A18 **)ldv_malloc(sizeof(struct A18*)*len);
  struct A18 *p;
  int i=0;
  int j;
  if(!array) return;
  for(; i<len; i++) {
    p = (struct A18 *)ldv_malloc(sizeof(struct A18));
    if(!p) goto err;
    array[i]=p;
  };
  return;
err:
  
  for(j=i-1; j>=0; j--) {
    free(array[j]);
  }
  free(array);
  return;
}

void main(void) {
  entry_point();
}