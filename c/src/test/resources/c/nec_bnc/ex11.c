extern int __VERIFIER_nondet_int();

int main(){
   int a[5];
   int len=0;

   int i;


   while(__VERIFIER_nondet_int()){

      if (len==4)
         len =0;

      a[len]=0;

      len++;
   }

   return 1;

   
}

/* cannot decide termination in while-loop. */
