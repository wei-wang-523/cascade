union Data
{
   int i;
   char c;
};

int main( )
{
   union Data* data = (union Data*)malloc(sizeof(union Data));

   data->i = 10;
   data->c = 'c';

//   printf( "data.i : %d\n", data.i);
//   printf( "data.c : %c\n", data.c);

   return 0;
}
