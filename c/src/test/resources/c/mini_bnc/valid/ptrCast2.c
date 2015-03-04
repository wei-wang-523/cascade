typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void *calloc (size_t __nmemb, size_t __size)
__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

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
