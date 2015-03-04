/*-- from blast tacas 06 examplex --*/
extern int __VERIFIER_nondet_int();

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
     ASSERT(1==0);
  }

  return 1;

}
