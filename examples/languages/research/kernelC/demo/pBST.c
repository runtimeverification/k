load kernelc-syntax
kmod KERNELC-BST is including KERNELC-SYNTAX 
syntax Pgm ::= pBST 
syntax #Id ::= val | newNode | insert | find | root | node | v | t
macro pBST =


#include <stdio.h>
#include <stdlib.h>
int *newNode(int v)
{
  int *node=(int *) malloc(3 * sizeof(int));
  *node=v;
  node[1]=node[2]=0;
  return node;
}


int* insert(int *t, int v)
{
  if (t == 0)
    return newNode(v);
  else if (v < *t) 
    t[1] = insert(t[1], v);
  else 
    t[2] = insert(t[2], v);
  return t;
}


int *find(int *t, int v)
{
  if (t == 0)
    return 0;
  else if (v == *t)
    return t;
  else if (v < *t)
    return find(t[1], v);
  else
    return find(t[2], v);
}

int main() {
  int* root=0;
  root=insert(root, 1);
  root=insert(root, 7);
  root=insert(root, 3);
  if (0==find(root,7)) printf("%d;", -1);
  if (0!=find(root,2)) printf("%d;", -1);
  root=insert(root, 2);
  root=insert(root, 2);
  if (0==find(root,2)) printf("%d;",-1);
  printf("%d;", 0);
  return 0;
}



endkm
