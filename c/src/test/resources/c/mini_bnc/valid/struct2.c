#include "../../../reserved.h"

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
