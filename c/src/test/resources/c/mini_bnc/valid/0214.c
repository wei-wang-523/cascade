typedef void *list_t[2];
typedef list_t *list_p;
typedef void *item_t[2];
typedef item_t *item_p;
typedef struct {
  item_t head;
  char text[0x100 + 1];
} *user_item_p;

int main() {
  static list_t srclist;
  
  list_p list = &srclist;
  item_p link = (*list)[0];
  if(link) {
    (*link)[0] = ((void *)0);
  }
  return 0;
}