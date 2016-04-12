#include "../../../reserved.h"

struct {char a; char b;} pair;

int main(){
  pair.a = 0xF;
  pair.b = 0xF;
  char * p = &pair.a;
  int * q = (int *)p;
  *q = 0;
  ASSERT(pair.b == 0);
}
