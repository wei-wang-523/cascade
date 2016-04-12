#include "../../../reserved.h"

int main(){
   int * a = (int*) malloc(2 * sizeof(int));
   a[0] = 0x0;
   
   char * d = (char *) a;
   int * b = (int *) (d+2);
   
   *b = 0xFFFF;
   
   ASSERT(a[0] == 0xFFFF0000);
   free(a);
   return 1;
}
