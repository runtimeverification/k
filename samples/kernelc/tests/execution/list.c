// Copyright (c) 2014 K Team. All Rights Reserved.
#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int value;
  struct listNode *next;
};


struct listNode* list_reverse(struct listNode *x)
{
  struct listNode *p;

  p = NULL;
  while(x != NULL) {
    struct listNode *y;

    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }

  return p;
}

struct listNode* list_append(struct listNode *x, struct listNode *y)
{
  struct listNode *p;
  if (x == NULL)
    return y;

  p = x;
  while (p->next != NULL)
    p = p->next;
  p->next = y;

  return x;
}


struct listNode* list_create(int n)
{
  struct listNode *x;

  x = NULL;
  while (n) {
    struct listNode *y;

    y = x;
    x = (struct listNode*) malloc(sizeof(struct listNode));
    x->value = n;
    x->next = y;

    n = n - 1;
  }

  return x;
}


void list_print(struct listNode* x)
{
  while(x != NULL) {
    printf("%d ", x->value);
    x = x->next;
  }
  printf("\n"); 
}

void list_free(struct listNode* x)
{
  while(x != NULL) {
    struct listNode *y;

    y = x->next;
    free(x);
    x = y;
  }
}


int main()
{
  struct listNode *x;
  struct listNode *y;

  x = list_create(5);
  printf("x: ");
  list_print(x);
  x = list_reverse(x);
  printf("reverse(x): ");
  list_print(x);
  list_free(x);

  x = list_create(3);
  printf("x: ");
  list_print(x);
  y = list_create(3);
  printf("y: ");
  list_print(y);
  x = list_append(x, y);
  printf("append(x, y): ");
  list_print(x);
  list_free(x);

  return 0;
}

