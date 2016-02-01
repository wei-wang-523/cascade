
int main(){
  while(__NONDET__()) {
  }
	
  return 1;	
}

/** invalid with option --merge-unroll and --lambda, since in the first
 * loop unrolling, return___NONDET__ is return___NONDET__0; the second
 * loop unrolling, return___NONDET__ is return___NONDET__1. When check
 * valid_access(return___NONDET__1) at merge point, the first-unrolling
 * will be invalid. (The path-constraint is true, but return___NONDET__1
 * is not declared yet.
 */
