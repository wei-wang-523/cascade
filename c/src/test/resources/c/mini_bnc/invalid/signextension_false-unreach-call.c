extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
  
  unsigned short int allbits = -1;
  short int signedallbits = allbits;
  unsigned int signedtounsigned = signedallbits;
  
  if (signedtounsigned == 4294967295) {
    goto ERROR;
  }
  
  return (0);
ERROR: __VERIFIER_error();
  return (-1);
}