#include <stdlib.h>
#include <stdio.h>
int* listReverseUnchecked(int* p);
int* listReverse(int* p);
int* listAppend(int* p, int n);
int listSum(int* p);

int main(void){
	int* head = malloc(sizeof(int) + sizeof(int*));
	*head = 20; 
	*((int**)(head + 1)) = NULL;
	// printf("%p\n", head);
	listAppend(head, 25);
	listAppend(head, 15);
	listAppend(head, 30);
	listAppend(head, 10);
	listAppend(head, 35);
	
	int* curr = head;
	while (curr != NULL){
		printf("%d,", *curr);
		curr = *((int**)(curr + 1));
	}
	printf("\n");
	
	int sum1 = listSum(head);
	int first = *head;
	head = listReverse(head);
	curr = head;
	while (curr != NULL){
		printf("%d,", *curr);
		curr = *((int**)(curr + 1));
	}
	printf("\n");	
	int last = *head;
	int sum2 = listSum(head);
	return (sum1 - sum2) + (last - first); // should be 15
}

int* listAppend(int* p, int n){
	int* x;
	// printf("%p\n", p);
    if (p != NULL) {
        x = p;
        while (*((int**)(x + 1)) != NULL) {
            x = *((int**)(x + 1));
        }		
		int* next = malloc(sizeof(int) + sizeof(int*));
        *((int**)(x + 1)) = next;
		*next = n;
		*((int**)(next + 1)) = NULL;
    }
	return p;
}

int listSum(int* p){
	int sum = 0;
	int* x;
    if (p != NULL) {
        x = p;
		sum += *x;
        while (*((int**)(x + 1)) != NULL) {
            x = *((int**)(x + 1));
			sum += *x;
        }		
	}
	return sum;
}

int* listReverse(int* p){
    if (p != NULL) {
		int* x = *((int**)(p + 1));
        *((int**)(p + 1)) = NULL;
        while(x != NULL) {
            int* tmp = *((int**)(x + 1));
            *((int**)(x + 1)) = p;
            p = x;
            x = tmp;
        }
    }
	return p;
}

