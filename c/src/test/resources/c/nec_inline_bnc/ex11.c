
int main(){
   int a[5];
   int len=0;

   int i;


   while(__NONDET__()){

      if (len==4)
         len =0;
	  ASSERT(valid(&(a[len])));
      a[len]=0;

      len++;
   }

   return 1;

   
}

/* cannot decide termination in while-loop. */