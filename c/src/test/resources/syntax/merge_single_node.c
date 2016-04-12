#include "reserved.h"

struct node {
  int value;
  struct node *next;
};

int main(struct node ***dst, struct node **data)
{
  struct node *node = *data;
  *data = node->next;
  node->next = ((void *)0);
  **dst = node;
  *dst = &node->next;
  return 0;
}