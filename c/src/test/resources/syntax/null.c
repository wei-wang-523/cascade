#include "../reserved.h"

struct T2{
  int *fst;
  int *snd;
};

struct T {
  int a;
  struct T2 link;
};

int main() {
  struct T* p = (struct T*) 0;
  unsigned long addr = (unsigned long) &(p->link);
  ASSERT(addr == sizeof(int));
  return 0;
}