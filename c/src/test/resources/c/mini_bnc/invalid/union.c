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
  ASSERT(data.i == 10 && data.c == 'c');
  return 0;
}

// Invalid. Burstall will return valid, since Burstall
// puts data.i and data.c in two separate arrays (Data_i)
// and (Data_c). The update of (Data_c) at the address
// data.c (= data.i) cannot be detected by (Data_i).