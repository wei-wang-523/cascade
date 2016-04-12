#include "../../../reserved.h"

typedef struct {
  void *lo;
  void *hi;
} TData;

static void alloc_data(TData *pdata)
{
  pdata->lo = malloc(16);
  pdata->hi = malloc(24);
}

static void free_data(TData fdata)
{
  void *lo = fdata.lo;
  void *hi = fdata.hi;
  
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