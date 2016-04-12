#include "../../../reserved.h"

int main (){
	char str[50] = "This is string.h library function";
	char* str1 = memset(str,'$',7);
	ASSERT(str1[3] == '$' && str[2] == '$');
	return 0;
}