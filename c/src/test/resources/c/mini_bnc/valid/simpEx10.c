#include "../../../reserved.h"

struct _addr {
	unsigned char len;
	unsigned char dat[16];
};
typedef struct _addr Addr;

struct _buffer {
	int dummy;
};
typedef struct _buffer Buffer;

int main(Addr *addr, Buffer *buf)
{
	addr = (Addr *)malloc(sizeof(Addr));
	buf = (Buffer *)malloc(sizeof(Buffer));
	ASSUME(addr->len >= 0 && addr->len < 16);
	ASSUME(addr->len <= 16);
  
  for(int idx =0; idx < addr->len; idx++) {
    addr->dat[idx-1] = 'c';
  }
  free(addr);
  free(buf);
  return 0;
}