typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

struct _buff {
  int data;
};
typedef struct _buff Buff;

int main() {
	Buff *buf = (Buff *)malloc(sizeof(Buff));
	buf->data = 1;
	ASSERT(buf->data == 1);
	return buf->data;
}
