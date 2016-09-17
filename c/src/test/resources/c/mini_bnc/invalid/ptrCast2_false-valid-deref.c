#include "../../../reserved.h"

typedef struct {char a; char b;} Pair;

int main(){
  Pair *p = (Pair *)malloc(sizeof(Pair));
  p->a = 1;
  p->b = 2;
  char *q = (char *)p;
  *q = 0;
  free(q); // Free the pointer after cast
  p->b = 3; // Invalid deref to a freed memory region
}
