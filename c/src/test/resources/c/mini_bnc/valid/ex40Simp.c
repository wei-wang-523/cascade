

extern char x[3], y[3];
extern int i;

int main() {

  
  i = 0;
  while(x[i] != 0){
    y[i] = x[i];
    i++;
  }
  
  return 0 ;
}
