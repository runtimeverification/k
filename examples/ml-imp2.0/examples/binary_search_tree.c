#include <stdlib.h>

struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};

struct treeNode* newNode(int v)
/*@ pre < config > < env > v |-> v0 </ env > < heap > heapFrame </ heap > 
                   < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap >
                      ?n |-> v0 : treeNode . val
                      ?n +Int 1 |-> 0 : treeNode . left
                      ?n +Int 2 |-> 0 : treeNode . right
                      heapFrame
                    </ heap >
                    < form > returns ?n </ form > </ config > */
{
  struct treeNode *node;
  node = (struct treeNode *)malloc(sizeof(struct treeNode));
  node->val = v;
  node->left=node->right = 0;
  return node;
}

struct treeNode* insert(struct treeNode *t, int v)
/*@ pre < config > < env > t |-> ?root v |-> v0 </ env >
                   < heap > tree(?root)(Tree) heapFrame </ heap > 
                   < form > isBst(Tree) </ form > </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > tree(?root)(?T) heapFrame </ heap > 
                    < form >
                      isBst(?T) /\ tree2mset(?T) === tree2mset(Tree) U {| v0 |}
                      /\ returns ?root
                    </ form > </ config > */
{
  if (t == 0)
    return newNode(v);
  if (v < t->val) t->left = insert(t->left, v);
    else t->right = insert(t->right, v);
  return t;
}


/*@ var ?n ?root : ?Int */
/*@ var v0 : FreeInt */
/*@ var ?rho : ?MapItem */
/*@ var heapFrame : FreeMapItem */
/*@ var ?T : ?Tree */
/*@ var Tree : FreeTree */

/*
void print(Tree t) {
  if (NULL != t) {
    print(t->left);
    printf("%d ", t->val);
    print(t->right);
  }
}

void print_tree(Tree t, int n) {
  if(NULL != t) {
    print_tree(t->left,n+2);
    for(int i=0;i<n;i++) printf(" ");
    printf("%d\n",t->val);
    print_tree(t->right,n+2);
  }
}

void printTree(Tree t) {
  print_tree(t,0);
  printf("\n");
}

Node* search(Tree t, int v) {
  while (NULL != t && t->val != v) 
    if (v > t->val) t = t->right; else t = t->left;
  return t;
}


Node* insert(Tree *t, int v) {
  while (NULL != *t)
    if (v > (*t)->val) t = &(*t)->right; else t = &(*t)->left;
  *t = newNode(v);
  return *t;
}

int main(void) {
  int v;
  Tree root[] = {NULL}; 
  while(scanf("%d",&v)) {
    insert(root,v);
    printTree(*root);
  }
  return 0;
}
*/
