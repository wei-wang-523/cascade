//#include <stdio.h>

struct {
  char*fp; // FILE* fp;
  int status;
} fs_t;


int main(int a, int b) {
  int status = 0, as, bs, flag=0;
  if(a > 0) {
    status = 0;
  }
  else {
    status = 1;
  }
  
  if(status == 1) {
    ASSUME(b > 0);
  }
  else {
    ASSUME(b <= 0);
  }
  
  if(a > 0)
    as = 0;
  else
    as = 1;
  if(b > 0)
    bs = 0;
  else
    bs = 1;
  
  if (bs == as) flag =1;
  ASSERT(flag == 0);
}
