int a[2];

int foo(int x){
	a[x]=1;
	return a[x];
}

int main(){
	int il;
	for(il=0; foo(il) && il < 2; ++il){}
	
	return 1;
}

// function call in the loop entry of for loop