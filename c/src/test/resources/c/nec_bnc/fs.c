#include "../../reserved.h"

struct list_head {
  struct list_head *next, *prev;
};

struct node {
  int value;
  struct list_head linkage;
};

struct list_head gl_list = { &(gl_list), &(gl_list) };

int main()
{
  struct node *node = (struct node *) malloc(sizeof *node);
  
  struct list_head *new = &node->linkage;
  struct list_head *head = &gl_list;
  
  head->next->prev = new;
  new->next = head->next;
  new->prev = head;
  head->next = new;
}