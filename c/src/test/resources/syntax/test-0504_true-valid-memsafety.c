#define NULL (void*) 0;

int main() {
  
  struct T {
    struct T* next;
    struct T* prev;
    int data;
  };
  
  struct T2 {
    struct T head;
    struct T2* next;
    struct T2* prev;
  };
  
  struct T2* x = malloc(sizeof(struct T2));
  if (!x) {
    abort();
  } else {
    x->next = NULL;
    x->prev = NULL;
    x->head.next = &x->head;
    x->head.prev = &x->head;
    x->head.data = 0;

    struct T* y = malloc(sizeof(struct T));
    if (!y) {
      abort();
    } else {
      y->next = x->head.next;
      y->next->prev = y;
      y->prev = &x->head;
      y->data = 0;
      x->head.next = y;
      y = NULL;
    }
  }
  return 0;
}
