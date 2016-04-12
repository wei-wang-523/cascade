/*-- from blast tacas 06 examplex --*/
#include "../../reserved.h"


int main(){
  
  int x,y;
  
  x = 0; y = 0;

  while(__VERIFIER_nondet_int()) {
    x++; y++;
  }
  
  while(x > 0){
    x--;
    y--;
  }
  
  if(y != 0){
     ASSERT(0);
  }

  return 1;

}
