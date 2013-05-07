int abs(int x, int y) {
  int result;
  if(x>=0) {
	  if(y > 0) {
		  result = x;
	  } else {
		  return 0;
	  }
  } else {
    result = -x;
  }
  return result;
}
