#include "../../../reserved.h"

struct _addr {
  unsigned char len;
  unsigned char dat[16];
};
typedef struct _addr Addr;

int main(Addr *addr)
{
	addr = (Addr*)malloc(sizeof(Addr));
	if (addr->len < 0 || addr->len >= 16) {
    free(addr);
		return 0;
	}
	addr->dat[addr->len] = 0xFF01; // test implicit conversion of assignment
  ASSERT(addr->dat[addr->len] == 1);
  free(addr);
	return 1;
}