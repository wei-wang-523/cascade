#define NULL (void*) 0
extern int __VERIFIER_nondet_int(void);

struct cell {
  struct cell* next;
};

int pc1 = 1;

void push()
{
  static struct cell *x1 = NULL;
  
  switch (pc1++) {
    case 1:
      return;
    case 2: {
      pc1 = 1;
      return;
    }
  }
}

int main()
{
  int i = 0;
  while (i < 2) {
    push(); i++;
  }
  ASSERT(1 == 0);
  return 0;
}
