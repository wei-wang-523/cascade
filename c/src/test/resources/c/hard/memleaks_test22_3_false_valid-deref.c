#define size_t int

typedef struct {
  int counter;
} ldv_atomic_t;

struct ldv_kref {
  ldv_atomic_t refcount;
};

struct ldv_list_head {
  struct ldv_list_head *next, *prev;
};

struct ldv_kobject {
  char *name;
  struct ldv_list_head entry;
  struct ldv_kref kref;
};

static void ldv_kobject_release(struct ldv_kref *kref) {
  struct ldv_kobject *kobj = ({
    const typeof( ((struct ldv_kobject *)0)->kref ) *__mptr = (kref);
    (struct ldv_kobject *)( (char *)__mptr - ((size_t) &((struct ldv_kobject *)0)->kref) );
  });
  
  char *name = kobj->name;
  free(kobj);
  
  if (name) {
    free(name);
  }
}

struct ldv_kobject *ldv_kobject_create(void) {
  struct ldv_kobject *kobj;
  
  kobj = (struct ldv_kobject *)malloc(sizeof(*kobj));
  if (!kobj)
    return 0;
  memset(kobj, 0, sizeof(*kobj));
  
  if (!kobj) return;
  
  (&(&kobj->kref)->refcount)->counter = 1;
  (&kobj->entry)->next = &kobj->entry;
  (&kobj->entry)->prev = &kobj->entry;
  
  return kobj;
}

static inline int ldv_atomic_sub_return(int i, ldv_atomic_t *v) {
  int temp;
  temp = v->counter;
  temp -= i;
  v->counter = temp;
  return temp;
}


void ldv_kobject_put(struct ldv_kobject *kobj)
{
  if (kobj) {
    if ((ldv_atomic_sub_return(1, (&(&kobj->kref)->refcount)) == 0)) {
      ldv_kobject_release(&kobj->kref);
    }
  }
}

void entry_point(void) {
  struct ldv_kobject *kobj;
  kobj = ldv_kobject_create();
  ldv_kobject_put(kobj);
  ldv_kobject_put(kobj);
}

void main(void) {
  entry_point();
}