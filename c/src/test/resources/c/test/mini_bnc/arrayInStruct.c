struct _addr {
  unsigned char len;
  unsigned char dat[16];
};
typedef struct _addr Addr;

int main(Addr *addr)
{
   ASSUME(addr);
   
   if (addr->len < 0 || addr->len >= 16) {
      return 0;
   }
   return 1;
}