#define MAXPATHLEN 2

char *fb_realpath(char *resolved)
{
  int rootd;
  char wbuf[MAXPATHLEN];

  if (resolved[0] == '/' && resolved[1] == '\0')
    rootd = 1;
  else
    rootd = 0;

  // steens-cfs treats resolved as Bottom ECR and won't merge 
  // *dest and resolved[0], resolved[1]
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