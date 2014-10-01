struct _nest {
  unsigned char dat[16];
};
typedef struct _nest nest;

struct _addr {
  unsigned char len;
  nest dat[16];
};
typedef struct _addr Addr;

int main(Addr *addr)
{
	addr = (Addr*)malloc(sizeof(Addr));
	ASSUME(addr);
	addr->dat[2].dat[2] = 'c';
	return 1;
}