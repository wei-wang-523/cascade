typedef struct list{
  struct list *prev;
  struct list *next;
  int data;
} list;

list** foo(int i)
{
   list *l1 = (list *)malloc(sizeof(list));
   list *l2 = (list *)malloc(sizeof(list));
   l1->data = 1; l1->prev = (void *)0;
   l2->data = 2; l2->next = (void *)0;
   list **p = i > 0 ? &(l1->next) : &(l2->prev);
   return p;
}

list** bar(int i) {
   list *l = (list *)malloc(sizeof(list));
   l->data = 0;
   list **p = i > 0 ? &(l->next) : &(l->prev);
   return p;
}

list** buz(int i) {
   list *l3 = (list *)malloc(sizeof(list));
   list *l4 = (list *)malloc(sizeof(list));
   l3->data = 1; l3->prev = (void *)0;
   l4->data = 2; l4->next = (void *)0;
   list **p = i > 0 ? &(l3->next) : &(l4->prev);
   int *q = &(l3->data);
   *(q + i) = 0;
   return p;
}