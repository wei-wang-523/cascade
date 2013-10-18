typedef struct account {
  int account_number;
  char *first_name;
  char last_name[1];
  int balance;
} acc;

int main() {
  acc r;
  r.balance = 1;
  acc *s;
//  s = (acc *)malloc(sizeof(acc));
  ASSUME(allocated(s, sizeof(acc)));
  s->account_number = 2;
  s->first_name = (char *)malloc(sizeof(char));
  s->first_name[0] = 'c';
  s->last_name[0] = 'd';
  ASSERT(	r.balance == 1 && s->account_number == 2 && s->first_name[0] == 'c' && s->last_name[0] == 'd');
  return 0;
}