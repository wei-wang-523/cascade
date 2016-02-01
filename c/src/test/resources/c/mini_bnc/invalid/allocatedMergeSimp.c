typedef struct foo{   
   int x;
   int* z;
} foo_t;

int main(int flag){
	foo_t * a;
	
	if(flag > 0) {
		a = (foo_t*)malloc(sizeof(foo_t));
		a->x = 1;
		ASSUME(a);
	}
	ASSERT(implies(flag > 0, a->x == 1));
	
	free(a);
	return 1;
}

// test resolve phi-node, should includes all the partitions, not the common ones.