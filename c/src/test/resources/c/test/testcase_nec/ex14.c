

int main(){
   int x,y;
   int a[5]; // a[10]
   x=1U;
   while (x <= 5U){ // x <= 10U
      y=5-x; // y=10-x
      a[y] = -1;
      x++;
   }

   return 1;

}

// Change LOC5, LOC7, LOC8, to limit the iteration times, 
// otherwise cascade will cause timeout.