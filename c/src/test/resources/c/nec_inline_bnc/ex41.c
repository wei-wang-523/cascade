extern int __VERIFIER_nondet_int();

extern char x[101], y[101], z[201];
int from,to,i,j,k;

void mainFunc() {  
	from = __VERIFIER_nondet_int();
	to = __VERIFIER_nondet_int();
	k = __VERIFIER_nondet_int();
	
	i = from;
	j = 0;
	while(x[i] != 0 && i < to){ // valid(&x[i]), from > 100
		ASSERT(valid(&x[i]) && valid(&z[j]));
		z[j] = x[i];
		i++;
		j++;
	}
	
	if(k >= 0 && k < j)
		if(z[k] == 0)
		{ERROR: goto ERROR;}  /* prove strlen(z) == j */
}