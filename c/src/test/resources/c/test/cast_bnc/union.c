union Data
{
   int i;
   char c;
};

int main( )
{
   union Data data;
   union Data* data_ = (union Data*)malloc(sizeof(union Data));

   data_->i = 10;
   data_->c = 'c';

   ASSERT(data_->i == 10 && data_->c == 'c');
   return 0;

   data.i = 10;
   data.c = 'c';

   ASSERT(data.i == 10 && data.c == 'c');
   return 0;
}
