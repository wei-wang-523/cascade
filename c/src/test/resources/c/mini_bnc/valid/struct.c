typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

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
  s = (acc *)malloc(sizeof(acc));

  s->account_number = 2;
  s->first_name = (char *)malloc(sizeof(char));
  s->first_name[0] = 'c';
  s->last_name[0] = 'd';
  ASSERT(r.balance == 1 && s->account_number == 2 && s->first_name[0] == 'c' && s->last_name[0] == 'd');
  free(s->first_name);
  free(s);
  return 0;
}