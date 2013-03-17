#define NULL 0;

struct NodeStruct {
  struct NodeStruct *next;
  int data;
};

typedef struct NodeStruct Node;

void create() { // Add newly create node to the head/root of list
  Node *root = NULL;
  int nondet;
  while(nondet) {
    Node *curr = (Node *)malloc(sizeof(Node));
    curr->next = root;
    root = curr;
    nondet++;
  }
}

void reverse(Node *root) {
  Node *first = root;
  Node *t, *e;
  e = first;
  first = NULL;
  while(e) {
    t = first;
    first = e;
    e = e->next;
    first->next = t;
  }
}

void filter(Node *root) {
  Node *first = root;
  
  Node *e = first;
  Node *prev = NULL;
  Node *del;
  int nondet;
  while(e) {
    if(e->data) {
      if (!prev) {
	prev = e;
	e = e->next;
	first = e;
	prev->next = NULL;
	prev = NULL;
      } else {
	e = e->next;
	del = prev->next;
	del->next = NULL;
	prev->next = e;
      }
    } else {
      prev = e;
      e = e->next;
    }
  }
}

void partition(Node *root) {
  Node *p_true = NULL;
  Node *p_false = NULL;
  Node *e = root;
  while (e) {
    if (e->data) {
      Node *tmp = p_true;
      p_true = e;
      e = e->next;
      p_true->next = tmp;
      tmp = NULL;
    } else {
      Node *tmp = p_false; 
      p_false = e;
      e = e->next;
      p_false->next = tmp;
      tmp = NULL;
    }
  }
}

void append(Node *l1, Node *l2) {
  Node *l = l1;
  Node *e = l1;
  Node *last = NULL;

  while (e) {
    last = e;
    e = e->next;
  }
  
  if (!last)
    l = l2;
  else 
    last->next = l2;
}

void insertBefore(Node *root, Node *pos, Node *n) {
  Node *e = root;
  Node *prev = NULL;
  
  while (e != pos) {
    prev = e;
    e = e->next;
  }
      
  if (!prev) {
    n->next = root;
  } else { 
    prev->next = n;
    n->next = e;
  }
}

void findPrev(Node *x, Node *y) {
  Node *e = x;
  Node *prev = NULL;

  while (e != y) {
    prev = e;
    e = e->next;
  }
}

void split(Node *root, Node *pos) {
  Node *e = root;
  Node *prev = NULL;

  while (e != pos && e) {
    prev = e;
    e = e->next;
  }
      
  if (prev)
    prev->next = NULL;
}

void contains(Node *root, Node *n) {
  Node *e = root;
  int result;
  
  while (e && e != n) {
    e = e->next;
  }
	 
  result = e != NULL;
}

void getLast(Node *root) {
  Node *e = root;
  Node *p = NULL;

  while (e) {
    p = e;
    e = e->next;
  }
}

void removeLast(Node *root) {
  Node *e = root;
  Node *l = NULL;
  Node *prev = NULL;
  
  while (e) {
    prev = l;
    l = e;
    e = e->next;
  }

  if (root != l) {
    prev->next = NULL;
  }
}

void remove(Node *root, Node *n) {
  Node *result = root;
  Node *e = root;
  Node *prev = NULL;

  while (e && e != n) {
    prev = e;
    e = e->next;
  }

  if (e) {
    if (prev) {
      prev->next = e->next;
    } else {
      result = root->next;
    }
    e->next = NULL;
  }
}

void traverse(Node *root) {
  Node *e = root;
  
  while (e) {
    e = e->next;
  }
}

int main() {
  return 1;
}
