#include <stdio.h>
#include <stdlib.h>

int counter = 0;

typedef struct struct_node {
	unsigned int m:1, c:1, v:1; /* booleans */
	unsigned int :2; // for testing purposes
	unsigned int blah:2; // for testing purposes
	//unsigned int xx:1;
	struct struct_node *l, *r;
	int value;
} * node;

void schorr_waite(node root) {
	node t = root; 
	node p = NULL;
	while (p != NULL || (t != NULL && ! t->m)) {
		if (t == NULL || t->m) {
			if (p->c) { /* pop */
				node q = t; 
				t = p; 
				p = p->r; 
				t->r = q;
			} else { /* swing */
				node q = t; 
				t = p->r; 
				p->r = p->l; 
				p->l = q; 
				p->c = 1;
			}
		} else { /* push */
			node q = p; 
			p = t; 
			t = t->l; 
			p->l = q; 
			p->m = 1; 
			p->c = 0; 
		}
	}
}
	
node createNode(){
	printf("creating new node %d\n", counter);
	node newNode = (node)malloc(sizeof(struct struct_node));
	newNode->c = 0;
	newNode->m = 0;
	newNode->v = 0;
	newNode->l = NULL;
	newNode->r = NULL;
	newNode->value = counter;
	newNode->blah = 0;
	newNode->blah = 1;
	counter++;
	return newNode;
}
node setLeft(node curr, node left){
	printf("Setting left child of %d to %d\n", curr->value, left->value);
	curr->l = left;
	return left;
}
node setRight(node curr, node right){
	printf("Setting right child of %d to %d\n", curr->value, right->value);
	curr->r = right;
	return right;
}

// algorithm  dft(x) 
   // visit(x) 
   // FOR each y such that (x,y) is an edge DO 
     // IF y was not visited yet THEN 
        // dft(y)
		
void showGraph(node this){
	if (this == NULL) { return; }
	if (this->v) { return; }
	printf("%d:m=%d:l=%d:r=%d\n", this->value, this->m, this->l->value, this->r->value);
	this->v = 1;
	showGraph(this->l);
	showGraph(this->r);
}

void cleanGraph(node this){
	if (this == NULL) { return; }
	if (this->v) {
		this->v = 0;
		this->m = 0;
		this->c = 0;
		cleanGraph(this->l);
		cleanGraph(this->r);
	}
}

int main(void) {
	node a, b, c, d, e;
	a = createNode();
	b = createNode();
	c = createNode();
	d = createNode();
	e = createNode();
	setLeft(a, b);
	setRight(a, c);
	setLeft(b, d);
	setRight(b, d);
	setLeft(c, b);
	setRight(c, a);
	setLeft(d, c);
	setRight(d, e);
	setLeft(e, e);
	setRight(e, a);
	
	node root = a;
	showGraph(root);
	cleanGraph(root);
	printf("Now running Schorr-Waite...\n");
	
	schorr_waite(root);
	showGraph(root);
	return 0;
}
