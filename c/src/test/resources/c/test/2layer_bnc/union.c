union Data
{
   int i;
   char c;
};

int main( )
{
   union Data data;

   data.i = 10;
   data.c = 'c';

//   printf( "data.i : %d\n", data.i);
//   printf( "data.c : %c\n", data.c);
   ASSERT(data.i == 10 && data.c == 'c');
   return 0;
}
