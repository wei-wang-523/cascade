#include <stddef.h>
#include <stdint.h>

#define NS_CMPRSFLGS (0xc0)

const uint8_t *ns_name_skip(uint8_t *p, const uint8_t *eom) {
  uint8_t *cp, n;

  cp = p;
  n = 0;

  if( cp < eom ) {
    n = *cp;
  }

  while( cp < eom && n != 0 ) {
    cp++;
    switch( n & NS_CMPRSFLGS ) {
    case 0:
      cp += n;
      if( cp < eom ) {
        n = *cp;
      }
      continue;

    case NS_CMPRSFLGS:
      cp++;
      break;

    default:
      return NULL;
    }
    break;
  }

  if( cp >= eom ) {
    return NULL;
  } else {
    return cp;
  }
}

int main() {
  uint8_t A[10];
  uint8_t *eom = &A[10];
  ns_name_skip(A,eom);
}
