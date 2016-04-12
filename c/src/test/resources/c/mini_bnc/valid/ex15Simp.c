#include "../../../reserved.h"

typedef struct{
   int * a;
   int * b;
   int * c;
} ptrStruct;

int main(){
   int x,y,z;
   ptrStruct A;
   A.a = &x;
   A.b = &y;
   A.c = &z;
   
   *(A.a) = 0;
   *(A.b) = 1;

   ptrStruct * ptr = &A;
   
   ASSERT(ptr->a == &x);
   
   return -1;
}