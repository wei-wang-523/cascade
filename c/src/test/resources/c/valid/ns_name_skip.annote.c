#include <stddef.h>
#include <stdint.h>

#define NS_CMPRSFLGS (0xc0)

const uint8_t *ns_name_skip(uint8_t *p, const uint8_t *eom) {
  uint8_t *cp, n;
  /* ANNOTE */
  const uint8_t *init_cp, *last_cp;
  /* ANNOTE */

  cp = p;
  n = 0;

  /* ANNOTE */
  init_cp = cp;
  last_cp = cp;
  /* ANNOTE */

  if( cp < eom ) {
    n = *cp;
  }

  /* INVARIANT: n = *cp && cp + sizeDn(cp) == init_cp + sizeDn(init_cp) && cp == last_cp */
  while( cp < eom && n != 0 ) {
    cp++;
    switch( n & NS_CMPRSFLGS ) {
    case 0:
      /* ASSERT is_label(last_cp) */
      cp += n;
      /* ASSERT rest(last_cp) == Dn(cp) */
      /* ANNOTE */
      last_cp = cp;
      /* ANNOTE */
      if( cp < eom ) {
        n = *cp;
      }
      continue;

    case NS_CMPRSFLGS:
      /* ASSERT is_indirect(last_cp) */
      cp++;
      break;

    default:
      return NULL;
    }
    break;
  }
  /* ASSERT cp == init_cp + sizeDn(init_cp) */
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
