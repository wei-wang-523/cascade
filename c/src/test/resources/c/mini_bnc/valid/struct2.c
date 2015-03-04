typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

struct {
  int account_number;
  char *first_name;
  char last_name[1];
  int balance;
} acc;

struct account{
  int account_number;
  char *first_name;
  char last_name[1];
  int balance;
} acc1;

int main() {
  acc.balance = 1;
  acc1.balance = 1;
  unsigned char *p = (unsigned char*) malloc(sizeof(unsigned char) * 10);
  free(p);
  return 0;
}
