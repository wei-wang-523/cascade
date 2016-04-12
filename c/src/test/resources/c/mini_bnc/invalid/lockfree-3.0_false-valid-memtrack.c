#include "../../../reserved.h"

struct cell {
  int data;
  struct cell* next;
};

struct cell *S;

int pc1 = 1;

void push()
{
  static struct cell *x1 = (void *) 0;
  
  switch (pc1++) {
    case 1:
      x1 = malloc(sizeof(*x1));
      x1->data = 0;
      x1->next = (void *) 0;
      return;
      
    case 2:
      x1->data = 4;
      return;
      
    default:
      pc1 = 1;
      return;
  }
}

int main()
{
  push();
  push();
  return 0;
}
