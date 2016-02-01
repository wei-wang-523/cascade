

extern char x[100], y[100];
extern int i;

int mainFunc() {

  
  i = 0;
  while(x[i] != 0){ // valid(x[i]), after 100 iter
    y[i] = x[i];
    i++;
  }
  
  return 0 ;
}
