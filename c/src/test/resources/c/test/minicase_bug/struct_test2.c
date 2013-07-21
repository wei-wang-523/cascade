typedef struct account {
  int account_number;
} acc;

int main(){
   int a[32];
   int x; // = __NONDET__();
   acc y;
   a[x%32] = y.account_number;
   return 1;
}
