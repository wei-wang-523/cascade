struct _addr {
  unsigned char len;
  unsigned char dat[16];
};
typedef struct _addr Addr;

int main(Addr *addr)
{
	addr = (Addr*)malloc(sizeof(Addr));
	ASSUME(addr);   
	if (addr->len < 0 || addr->len >= 16) {
		return 0;
	}
	ASSERT(valid(&addr->dat[addr->len]));
	return 1;
}