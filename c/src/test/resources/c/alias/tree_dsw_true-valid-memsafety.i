extern int __VERIFIER_nondet_int(void);

int main() {
 struct TreeNode {
  struct TreeNode* left;
  struct TreeNode* right;
 };
 struct StackItem {
  struct StackItem* next;
  struct TreeNode* node;
 };
 struct TreeNode* root = malloc(sizeof(*root)), *n;
 root->left = ((void *)0);
 root->right = ((void *)0);
 while (__VERIFIER_nondet_int()) {
  n = root;
  while (n->left && n->right) {
   if (__VERIFIER_nondet_int())
    n = n->left;
   else
    n = n->right;
  }
  if (!n->left && __VERIFIER_nondet_int()) {
   n->left = malloc(sizeof(*n));
   n->left->left = ((void *)0);
   n->left->right = ((void *)0);
  }
  if (!n->right && __VERIFIER_nondet_int()) {
   n->right = malloc(sizeof(*n));
   n->right->left = ((void *)0);
   n->right->right = ((void *)0);
  }
 }
 struct TreeNode sentinel;
 n = root;
 struct TreeNode* pred = &sentinel;
 struct TreeNode* succ = ((void *)0);
 while (n != &sentinel) {
  succ = n->left;
  n->left = n->right;
  n->right = pred;
  pred = n;
  n = succ;
  if (!n) {
   n = pred;
   pred = ((void *)0);
  }
 }
 if (pred != root)
  ((struct TreeNode*)((void *)0))->left = ((void *)0);
 n = ((void *)0);
 struct StackItem* s = malloc(sizeof(*s)), *st;
 s->next = ((void *)0);
 s->node = root;
  st = s;
  s = s->next;
  n = st->node;
  free(st);
  if (n->left) {
   st = malloc(sizeof(*st));
   st->next = s;
   st->node = n->left;
   s = st;
  }
  if (n->right) {
   st = malloc(sizeof(*st));
   st->next = s;
   st->node = n->right;
   s = st;
  }
  free(n);
 return 0;
}
