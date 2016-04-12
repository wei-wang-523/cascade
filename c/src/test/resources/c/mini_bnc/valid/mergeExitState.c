#include "../../../reserved.h"

int main() {
  while (__VERIFIER_nondet_int()) {}
  
  return 0;
}

/* Test the merge exit state edge with merge unroll:
 * when merge the exit edge of #0 unroll and #1 unroll,
 * the assume(!CASCADE.return___VERIFIER_nondet_int) 
 * statement represents two different variables:
 * - CASCADE.return___VERIFIER_nondet_int_0
 * - CASCADE.return___VERIFIER_nondet_int_1
 * Merge the states after encoding the loop exit edge
 * not the source states of the edge
 */