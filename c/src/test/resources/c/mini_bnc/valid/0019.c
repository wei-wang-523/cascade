typedef long unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

typedef struct {
  void *lo;
  void *hi;
} TData;

static void alloc_data(TData *pdata)
{
  pdata->lo = malloc(16);
  pdata->hi = malloc(24);
}

static void free_data(TData data)
{
  void *lo = data.lo;
  void *hi = data.hi;
  
//  if (lo == hi)
//    return;
  
  free(lo);
  free(hi);
}

int main() {
  TData data;
  alloc_data(&data);
  free_data(data);
  return 0;
}