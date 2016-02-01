
int * main (int x){
	
	int * a;
	
	
	ASSUME(x >= 0);
	
	a = (int *) malloc( x * sizeof(int));
	
	ASSUME(a);
	
	ASSERT(forall(idx, implies(idx >=0 && idx < x, valid(&a[idx]))));
	return a;
	
}

// test forall formula in assertion with valid predicate.
// design for lambda encoding, to test if both z3 and cvc4
// can handle quantified formula parsed via CExpressionEncoder properly