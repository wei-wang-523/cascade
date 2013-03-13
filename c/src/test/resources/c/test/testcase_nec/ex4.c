int a[2]; //a[10]

int foo(int x){
	a[x]=1;
	return a[x];
}

int main(){
	int il;
	for(il=0; foo(il) && il  < 2; ++il){} // il < 10
	
	for(il=0; il < 2 && foo(il) ; ++il){} // il < 10
	
	return 1;
}

// LOC1/10/12: change il < 10 to il < 2. 

/* Feasibility. */
