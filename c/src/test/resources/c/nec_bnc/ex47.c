//#include <stdlib.h>

typedef int DIST;


int main(int h, int w, int k){

   DIST **lut; // lookup table, 2D array of structures
   DIST *array;
   int x, y;
  
   ASSUME(h > 0);
   ASSUME(w > 0);
   //   fSft__assume(k > 0 && k < h*w);
   
   lut = (DIST**)malloc(sizeof(DIST*)*h);
   lut[0] = (DIST*)malloc(sizeof(DIST)*h*w);
   for (y=0; y<h; y++)
     lut[y] = lut[0] + w*y;
   
   array = lut[0];
   //    fSfT_assert(array[k] == lut[k/w][k%w]);
   
   free(lut[0]);
   free(lut);
   
   return 1;
}
