extern int __VERIFIER_nondet_int();

int main(){
   int a[32];
   int x = __VERIFIER_nondet_int();

   a[x%32] = 1;
   
}

/* 
   Benchmark ex13.c comment 
   (added in version 1.1, January 2011, by Franjo Ivancic, ivancic@nec-labs.com)

   Note that the signed integer x may contain a negative number. Thus, the 
   modulo operation may yield a value that is less than 0 causing a buffer 
   underrun. 

   Thanks to Lucas Cordeiro for pointing out the omission of this bug in the bugs file. 
*/
