// based on 20020920-1.c in gcc c torture tests
#include <stdio.h>
struct B {
	int x;
	int y;
};

struct A {
	int z;
	struct B b;
};

// struct B b = { 4, 5 };
// struct A a = { 6, b };

static struct A f () {
	struct B b = { 0, 1 };
	struct A a = { 2, b };
	//debug();
	printf("in f():\n");

	printf("b.x = %d\n", b.x);
	printf("b.y = %d\n", b.y);
	
	int test1 = a.z;
	int test2 = a.b.x;
	int test3 = a.b.y;
	printf("%d\n", test1);
	printf("%d\n", test2);
	printf("%d\n", test3);
	return a;
}

int main (void) {
	struct A a = f();
	printf("in main():\n");
	int test1 = a.z;
	int test2 = a.b.x;
	int test3 = a.b.y;
	printf("%d\n", test1);
	printf("%d\n", test2);
	printf("%d\n", test3);
	//debug();
	return 0;
}
