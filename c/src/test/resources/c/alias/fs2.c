#include "../../reserved.h"

struct list_head {
  struct list_head *next, *prev;
};
static inline int list_empty(struct list_head *head)
{
  return head->next == head;
}
static inline void __list_add(struct list_head *new,
                              struct list_head *prev,
                              struct list_head *next)
{
  next->prev = new;
  new->next = next;
  new->prev = prev;
  prev->next = new;
}
static inline void __list_del(struct list_head *prev, struct list_head *next)
{
  next->prev = prev;
  prev->next = next;
}
static inline void list_add(struct list_head *new, struct list_head *head)
{
  __list_add(new, head, head->next);
}
static inline void list_del(struct list_head *entry)
{
  __list_del(entry->prev, entry->next);
  entry->next = (void *) 0;
  entry->prev = (void *) 0;
}
static inline void list_move(struct list_head *list, struct list_head *head)
{
  __list_del(list->prev, list->next);
  list_add(list, head);
}
struct node {
  int value;
  struct list_head linkage;
};
struct list_head gl_list = { &(gl_list), &(gl_list) };
static void gl_insert(int value)
{
  struct node *node = malloc(sizeof *node);
  if (!node)
    abort();
  node->value = value;
  list_add(&node->linkage, &gl_list);
}
static void gl_read()
{
  do {
    gl_insert(__VERIFIER_nondet_int());
  }
  while (__VERIFIER_nondet_int());
}
static void gl_destroy()
{
  struct list_head *next;
  while (&gl_list != (next = gl_list.next)) {
    gl_list.next = next->next;
    free(((struct node *)((char *)(next)-(unsigned long)(&((struct node *)0)->linkage))));
  }
}
static int val_from_node(struct list_head *head) {
  struct node *entry = ((struct node *)((char *)(head)-(unsigned long)(&((struct node *)0)->linkage)));
  return entry->value;
}
static struct list_head* gl_seek_max()
{
  struct list_head *pos, *max_pos = ((void *)0);
  int max;
  if (list_empty(&gl_list))
    return ((void *)0);
  else {
    max_pos = gl_list.next;
    max = val_from_node(max_pos);
  }
  for (pos = (max_pos)->next; pos != (max_pos); pos = pos->next) {
    const int value = val_from_node(pos);
    if (value < max)
      continue;
    max_pos = pos;
    max = value;
  }
  return max_pos;
}
static void gl_sort()
{
  if (list_empty(&gl_list))
    return;
  struct list_head dst = { &(dst), &(dst) };
  struct list_head *max_pos;
  while ((max_pos = gl_seek_max()))
    list_move(max_pos, &dst);
  dst.next->prev = &gl_list;
  dst.prev->next = &gl_list;
  gl_list = dst;
}
int main()
{
  gl_read();
  gl_sort();
  gl_destroy();
  return 0;
}