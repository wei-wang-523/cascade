struct ldv_kobject {
  char *head;
  char *name;
};

void main(void) {
  int *kobj = (int*) malloc(10 * sizeof(int));
  free(kobj);
  *kobj = 0;
}