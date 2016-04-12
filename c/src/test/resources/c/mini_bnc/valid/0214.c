#include "../../../reserved.h"

int i = 0;

typedef void *list_t[2];
typedef list_t *list_p;
typedef enum {
  LIST_BEG,
  LIST_END
} end_point_t;

typedef void *item_t[2];
typedef item_t *item_p;
typedef enum {
  ITEM_PREV,
  ITEM_NEXT
} direction_t;

typedef struct {
  item_t head;
  char text[0x100 + /* terminating zero */ 1];
} *user_item_p;

item_p create_item(item_p link)
{
  user_item_p item = malloc(sizeof *item);
  item->head[ITEM_NEXT] = link;
  item->head[ITEM_PREV] = ((void *)0);
  item->text[0] = '\0';
  item_p head = &item->head;
  
  if (link)
    (*link)[ITEM_PREV] = head;
  
  return head;
}

void append_one(list_p list)
{
  item_p item = create_item((*list)[LIST_BEG]);
  
  (*list)[LIST_BEG] = item;
  
  if (((void *)0) == (*list)[LIST_BEG])
    (*list)[LIST_BEG] = item;
  
  if (((void *)0) == (*list)[LIST_END])
    (*list)[LIST_END] = item;
}

void remove_one(list_p list)
{
  free((*list)[LIST_BEG]);
  memset(*list, 0, sizeof *list);
  return;
}

int main()
{
  static list_t list;
  append_one(&list);
  remove_one(&list);
  
  return 0;
}