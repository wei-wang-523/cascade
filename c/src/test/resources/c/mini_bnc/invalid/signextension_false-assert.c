#include "../../../reserved.h"

int main() {
  
  unsigned short int allbits = -1;
  short int signedallbits = allbits;
  unsigned int signedtounsigned = signedallbits;
  ASSERT(signedtounsigned != 4294967295);
  
  return (0);
}