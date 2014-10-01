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
