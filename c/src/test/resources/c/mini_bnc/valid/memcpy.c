typedef unsigned long size_t;
extern void *memcpy(void *dest, const void *src, size_t n);

int main (){
	const char src[50] = "http://www.tutorialspoint.com";
	char dest[50];
	memcpy(dest, src, 4);
	ASSERT(dest[2] == 't');
	return 0;
}