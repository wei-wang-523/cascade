struct _addr {
	unsigned char len;
	unsigned char dat[16];
};
typedef struct _addr Addr;

int f1(Addr *addr);

int main(Addr *addr)
{
	ASSUME(addr);
	return f1(addr);
}

int f1(Addr *addr)
{
	int i = (int)addr->len;
	
	int ret1;
    
	while (i ) {
		addr->dat[i - 1] = 1;
		if (ret1 != 0) {
			return ret1;
		}
		i = i - 1;
	}  
	return 0;
}

// test return in loop body -- loop will be iterated once more to reach the return statement