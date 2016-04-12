#include "../../../reserved.h"

struct _buff {
  int dummy;
};
typedef struct _buff Buff;

int main() {
  Buff buf;
  buf.dummy = 1;
  ASSERT(buf.dummy == 1);
  return buf.dummy;
}
