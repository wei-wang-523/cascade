typedef struct list{
  struct list *prev;
  struct list *next;
  int data;
} list;

typedef struct dlist{
  struct dlist *prev;
  struct dlist *next;
} dlist;

list** foo1(int i)
{
   list *l1 = (list *)malloc(sizeof(list));
   list *l2 = (list *)malloc(sizeof(list));
   l1->data = 1; l1->prev = (void *)0;
   l2->data = 2; l2->next = (void *)0;
   list **p = i > 0 ? &(l1->next) : &(l2->prev);
   return p;
}

list** foo2(int i)
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
   list **p = foo1(i);
   *(p + i) = 0;
   return p;
}

dlist qux(int i) {
   list **p = foo2(i);
	 dlist* q = (dlist *)p;
	 q->next = q;
   return *q;
}