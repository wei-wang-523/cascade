typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

struct _addr {
  unsigned char len;
  unsigned char dat[16];
};
typedef struct _addr Addr;

int main(Addr *addr)
{
	addr = (Addr*)malloc(sizeof(Addr));
	if (addr->len < 0 || addr->len >= 16) {
		return 0;
	}
	addr->dat[addr->len] = 0xFF01; // test implicit conversion of assignment
  ASSERT(addr->dat[addr->len] == 1);
	return 1;
}