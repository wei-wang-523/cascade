//#include <stdlib.h>

#define INIT_SIZE 1 // INIT_SIZE 100

typedef struct _vector
{
	int size; // size_t size;
	int capacity; // size_t capacity;
	int *data;
} Vector;

Vector* create_vector()
{
	Vector *node;

	node = (Vector *) malloc(1 * sizeof(Vector));
	node->size = 0;
	node->capacity = INIT_SIZE;
	node->data = (int *)malloc(node->capacity* sizeof(int));
	ASSUME(node->data);
	return node;
}

void memcpy(int* pvTo, int* pvFrom, int size) 

{ 
	int* pbTo = pvTo; 	
	int* pbFrom = pvFrom; 
	
	while(size-->0)
		*(pbTo+size) = *(pbFrom+size);
}

void push_back(Vector *vct, int value)
{
	int *tmp;
	ASSERT(vct -> size <= vct -> capacity);
	if (vct->size >= vct->capacity)
	{
		vct->capacity += INIT_SIZE;
		tmp = (int*) malloc (vct->capacity * sizeof(int));
		ASSUME(tmp != NULL);
		memcpy(tmp, vct->data, (vct->capacity - INIT_SIZE)*sizeof(int));
		free(vct->data);
		vct->data = tmp;
	}
        
	vct->data[vct->size++] = value;
}

int main(int n){
   int i;
   Vector * a;
   ASSUME(n > 0);
   
   a = create_vector();
   
   for (i =0; i<n; i++) 
   {
       push_back(a, i);
   }
   
   ASSERT(a->size == n);

   return 1;
}

// LOC1: comment include <stdlib.h>, cascade cannot analyze it for now.
// LOC3: change INIT_SIZE from 100 to 1.
// LOC7: type size_t is not declared before, replace it with int.
// LOC8: type size_t is not declared before, replace it with int.
// LOC46: code bug with function name.
