//#include <stdlib.h>

typedef struct dist_{
   
  int x;
  int y;
  int z;
  
} DIST;


int main(int h, int w){
  
  DIST **lut; // lookup table, 2D array of structures
  int x, y;
  
  h = 2; //  ASSUME(h > 0);
  w = 1; //ASSUME(w > 0);
   
  lut = (DIST**)malloc(sizeof(DIST*)*h);
  lut[0] = (DIST*)malloc(sizeof(DIST)*h*w);
  for (y=0; y<h; y++)
    lut[y] = lut[0] + w*y; //pointer arithmetic: multiplied by the size of the type of the pointer lut[y] = lut[0] + w*y*sizeof(DIST)
  
  ASSERT(lut[0][h*w-1].x == lut[h-1][w-1].x);
  
  free(lut[0]);
  free(lut);
  
  return 1;
}
