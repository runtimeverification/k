#include <stdio.h>
#include <stdlib.h>

struct list_el {
   int val;
   struct list_el * next;
};

typedef struct list_el item;

item* listReverse(item* p);
item* listAppend(item* p, int n);

item* listAppend(item* p, int n){
	item* x;
	if (p == NULL){
		p = (item*)malloc(sizeof(item));
		p->val = n;
		p->next = NULL;	
	} else {
        x = p;
        while (x->next != NULL) {
            x = x->next;
        }		
		item* next = (item*)malloc(sizeof(item));
        x->next = next;
		next->val = n;
		next->next = NULL;
    }
	return p;
}

item* listReverse(item* p){
    if (p != NULL) {
		item* x = p->next;
        p->next = NULL;
        while(x != NULL) {
            item* tmp = x->next;
            x->next = p;
            p = x;
            x = tmp;
        }
    }
	return p;
}

int main(void){
	item* head = listAppend(NULL, 20);
	listAppend(head, 25);
	listAppend(head, 15);
	listAppend(head, 30);
	listAppend(head, 10);
	listAppend(head, 35);
	
	item* curr = head;
	while (curr != NULL){
		printf("%d,", curr->val);
		curr = curr->next;
	}
	printf("\n");
	
	int first = head->val;
	head = listReverse(head);
	curr = head;
	while (curr != NULL){
		printf("%d,", curr->val);
		curr = curr->next;
	}
	printf("\n");	
	
	return 0;
}
