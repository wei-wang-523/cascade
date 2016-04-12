#include "../../../reserved.h"

struct ldv_kobject {
  char *head;
  char *name;
};

int main(void) {
  int *kobj = (int*) malloc(10 * sizeof(int));
  free(kobj);
  *kobj = 0;
  return 0;
}