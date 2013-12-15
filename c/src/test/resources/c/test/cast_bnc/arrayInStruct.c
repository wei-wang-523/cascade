typedef struct data
{
   int i;
   char c[20];
} Data;

int main( )
{
   Data* data = (Data*)malloc(sizeof(Data));
   Data c1[20];
   data->i = 10;
   data->c[0] = 'c';
   (c1[2]).c[0] = 'd';
	 char c[20];
	 c[19] = 'e';
   ASSERT(data->i == 10 && data->c[0] == 'c' && c1[2].c[0] == 'd' && c[19] == 'e');
   return 0;
}
