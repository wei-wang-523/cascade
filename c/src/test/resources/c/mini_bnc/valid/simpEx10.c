typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

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