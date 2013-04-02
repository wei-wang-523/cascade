#define NULL 0;

struct NodeStruct {
  struct NodeStruct *next;
  struct NodeStruct *prev;
  int data;
};

typedef struct NodeStruct Node;

void create() { // Add newly create node to the head/root of list
  Node *root = NULL;
  int nondet;
  while(nondet) {
    Node *curr = (Node *)malloc(sizeof(Node));
    curr->next = root;
    curr->prev = NULL;
    if(root)
      root->prev = curr;
    root = curr;
    nondet++;
  }
}

void reverse(Node *root) {
  Node *first = root;
  Node *pre = NULL;
  while(first) {
    pre = first->prev;
    first->prev = first->next;
    first->next = pre;
    first = first->prev;
  }
  if(pre)
    first = pre->prev;
  else
    first = root;
}

void filter(Node *root) {
  Node *e = root;
  Node *del = NULL;
  while(e) {
    if(e->data) {
	del = e;
	if(e->prev) // e->prev != NULL
	  e->prev->next = e->next;
	if(e->next) // e->next != NULL
	  e->next->prev = e->prev;
	e = e->next;
	del->next = del->prev = NULL;
    } else {
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
      p_true->prev = NULL;
      if(tmp)
	tmp->prev = p_true;
    } else {
      Node *tmp = p_false;
      p_false = e;
      e = e->next;
      p_false->next = tmp;
      p_false->prev = NULL;
      if(tmp)
	tmp->prev = p_false;
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
  else {
    last->next = l2;
    l2->prev = last;
  }
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
    root->prev = n;
  } else { 
    prev->next = n;
    n->prev = prev;
    n->next = e;
    e->prev = n; // e != NULL
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

   if (prev) {
     prev->next = NULL;
     pos->prev = NULL;
   }
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
     l = e;
     e = e->next;
   }

   if (root != l) {
     l->prev->next = NULL;
     l->prev = NULL;
   }
 }


 void remove(Node *root, Node *n) {
   Node *result = root;
   Node *e = root;
   Node *prev = NULL;

   while (e && e != n) {
     e = e->next;
   }

   if (e) {
     if (e->next)
       e->next->prev = e->prev;

     if (e->prev) 
       e->prev->next = e->next;
     else // e->prev == NULL
       result = root->next;
     e->next = NULL;
     e->prev = NULL;
   }
 }

 void traverse(Node *root) {
   Node *e = root;

   while (e) {
     e = e->next;
   }
 }

 void max(Node *root) {
   Node *e = root;
   int maxData = 0;

   while (e) {
     if(e->data > maxData)
       maxData = e->data;
     e = e->next;
  }
}

int main() {
  return 1;
}
