#define MAXPATHLEN 2

char *fb_realpath(char *resolved)
{
  int rootd;
  char wbuf[MAXPATHLEN];

  if (resolved[0] == '/' && resolved[1] == '\0')
    rootd = 1;
  else
    rootd = 0;

  char *dest = resolved;
  char *src = wbuf;
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

  return resolved;
}
