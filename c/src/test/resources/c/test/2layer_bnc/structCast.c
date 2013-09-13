typedef struct account {
  int account_number;
  char *first_name;
//  char last_name[1];
  int balance;
} acc;

typedef struct account_1 {
  int account_number;
  char *first_name;
//  char last_name[1];
  int balance;
  int more;
} acc1;

int main() {
//  acc r;
//  r.balance = 1;
  acc *s;
  s = (acc *)malloc(sizeof(acc));
  s->account_number = 2;
  s->first_name = (char *)malloc(sizeof(char));
  s->first_name[0] = 'c';
//  s->last_name[0] = 'd';
  acc1* r1 = (acc1 *)s;
  ASSERT(r1->account_number == 2);
  return 0;
}
