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
	ASSUME(addr);
	ASSUME(addr->len >= 0 && addr->len < 16);
	ASSUME(addr->len <= 16);
    int i = (int) addr->len;
	ASSERT(i >= 0 && i <= addr->len && 
		   implies(
				   i > 0 && i <= addr-> len, 
				   valid(&addr->dat[i - 1])));
	return 0;
}