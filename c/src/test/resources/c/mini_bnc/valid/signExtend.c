int main() {
  unsigned int allOne = -1;
  
  int castToInt = allOne;
  long castToLong = allOne;
  long castToLong2 = castToInt;
  unsigned long castToULong = allOne;
  
  ASSERT(castToInt == -1);
  ASSERT(castToLong == 4294967295UL);
  ASSERT(castToLong2 == -1);
  ASSERT(castToULong == 4294967295UL);
  
  return (0);
}