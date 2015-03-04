typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

typedef struct account{
  int account_number;
  char *first_name;
  char last_name[1];
  int balance;
} acc;

int main() {
  acc s1;
	acc s2;
	s1.account_number = 2;
	s1.balance = 1;
	s2 = s1;
  ASSERT(s2.account_number == 2);
  return 0;
}
