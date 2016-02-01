struct foo{
   int x[1000];
};

int make_null(struct foo * hoo){
   int i;
   for (i=999; i >= 0; i--)
      hoo->x[i]=0;
   return 0;

}

int main(){
   struct foo hoo;
   int j = 1;
   if (j == 0) {
      make_null((struct foo*) 0);
   }
   make_null(&hoo);

   return 1;
}


// used for testing declare fresh variable for local variable in the function called, 
// especially for the lambda-based memory safety predicates updating, while the trace
// via assuming j==0, is infeasible, will be disregarded at phi-node join. Thus, those
// local variable declarations that affected predicates updating will be disregarded too.

// but the second function call make_null(&hoo), those local variables in make_null function 
// will be declared again, this time, it is valid, therefore, we should create fresh 
// left-variable bindings for them again.