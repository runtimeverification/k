#include <stdio.h>

int main(void){
	int x1 = 0;
	int x2 = {0};
	char x3[] = "hi";
	char x4[2] = "hi";
	char x13[3] = "hi";
	struct {char a[2]; char b[3];} x15;
	x15.a[0] = 'h'; x15.a[1] = 'i';
	x15.b[0] = 'h'; x15.b[1] = 'i'; x15.b[2] = '\0';
	struct {char a[2]; char b[3];} x14 = {"hi", "hi"};
	unsigned char x5[] = "hi";
	char x6[] = {"hi"};
	char x7[2] = {"hi"};
	
	struct { char a[3]; } x11 = {"hi"};
	printf("%c%c\n", x11.a[0], x11.a[1]);
	struct { char* a; } x12 = {"hi"};
	printf("%c%c\n", x12.a[0], x11.a[1]);
	char x8[3] = {1, 2};
	int x9[3] = {1, 2, 3};
	int x10[] = {5, 6, 7};
	int x16[] = {5};
	struct {int a; int b; int c[2]; int d;} x17 = {.b = 2, 3, 4, 5};
	struct {int a; int b;} x18[2] = {{1, 2}, {3}};
	struct {int a; int b;} x19[2] = {1, 2, 3};
	return 0;
}
