#include "../../reserved.h"

char *(cstrcat)(char *s1, const char *s2)
{
  char *s = s1;
  /* Move s so that it points to the end of s1.  */
  while (*s != '\0')
    s++;
  /* Do the copying in a loop.  */
  while ((*s++ = *s2++) != '\0')
    ;               /* The body of this loop is left empty. */
  /* Return the destination string.  */
  return s1;
}

int main() {
  int length1 = 1;
  int length2 = 2;
  int length3 = 1;
  
  char* nondetString1 = (char*) alloca(length1 * sizeof(char));
  char* nondetString2 = (char*) alloca(length2 * sizeof(char));
  nondetString1[length1-1] = '\0';
  nondetString2[length3-1] = '\0';
  cstrcat(nondetString2,nondetString1);
  return 0;
}

/**
 * "CASCADE_return_cstrcat_0.function(main)" is the auxiliary variable
 * representing the result returned by function call:
 *   "cstrcat(nondetString2)"
 *
 * "CASCADE_return_cstrcat.function(cstrcat)" is the auxiliary variable
 * representing the return value of function "cstrcat".
 * 
 * DSA merges them in a single alias group; CFS doesn't merge them.
 * The question is whether they are aliased or not.
 * 
 * There is a information flow from "CASCADE_return_cstrcat" to
 * "CASCADE_return_cstrcat_0", as an implicit assignment:
 *     CASCADE_return_cstrcat_0 = CASCADE_return_cstrcat.
 *
 * However, they are NOT aliased and instead their points-to content are.
 */