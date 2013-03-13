//#define MAXPATHLEN 2


int strlen(const char *st)
{
  int ret = 0;
  while (*st != '\0') {
    ret++;
    st++;
  }
  return ret;
}


char *strcat(char * dest, const char *src) {
  char *ret;
  ret = dest;
  while(*dest!='\0') {
    dest++;
  }
  while (*src!= '\0') {
    *dest = *src;
    dest++;
    src++;
  }
  *dest = *src;
  return ret;
}


char *fb_realpath(char *resolved)
{
  int rootd;
  char wbuf[MAXPATHLEN];

  if (resolved[0] == '/' && resolved[1] == '\0')
    rootd = 1;
  else
    rootd = 0;
	  
  if (strlen(resolved) + strlen(wbuf) + rootd + 1 > MAXPATHLEN) {
    return resolved;
  } else {
    if (rootd == 0) /* 1 is correct, 0 is incorrect */
      (void) strcat(resolved, "/");
    (void) strcat(resolved, wbuf);
  }
  return resolved;
}


int main() {
  char resolved[MAXPATHLEN];
  resolved[0] = '\0';
  fb_realpath(resolved);

}
