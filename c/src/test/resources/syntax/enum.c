#include "../reserved.h"

typedef enum {
  TRUE,
  FALSE
} BOOLEAN;

int main() {
  BOOLEAN boolVal = TRUE;
  ASSERT(boolVal != FALSE);
  return 0;
}