#include <stdio.h>
#include <stdlib.h>

int sec26(void){
	int y1[4][3] = {
		{1, 3, 5},
		{2, 4, 6},
		{3, 5, 7},
	};
	int y2[4][3] = {1, 3, 5, 2, 4, 6, 3, 5, 7};
	for (int i = 0; i < 4; i = i + 1){
		for (int j = 0; j < 3; j = j + 1){
			printf("y1[%d][%d]=%d\n", i, j, y1[i][j]);
			if (y1[i][j] != y2[i][j]) {
				return 1;
			}
		}
	}
	return 0;
}
int sec27(void){
	int z1[4][3] = {
		{1}, {2}, {3}, {4}
	};
	int z2[4][3] = {1, 0, 0, 2, 0, 0, 3, 0, 0, 4, 0, 0};
	for (int i = 0; i < 4; i = i + 1){
		for (int j = 0; j < 3; j = j + 1){
			printf("z1[%d][%d]=%d\n", i, j, z1[i][j]);
			if (z1[i][j] != z2[i][j]) {
				return 1;
			}
		}
	}
	return 0;
}
int sec28(void){
	struct {int a[3], b;} w1[] = {{1}, 2};
	struct {int a[3], b;} w2[2] = {[0].a[0] = 1, [1].a[0] = 2};
	for (int i = 0; i < 2; i = i + 1){
		for (int j = 0; j < 3; j = j + 1){
			printf("w1[%d].a[%d]=%d\n", i, j, w1[i].a[j]);
			if (w1[i].a[j] != w2[i].a[j]) {
				return 1;
			}
			if (w1[i].b != w2[i].b) {
				return 1;
			}
		}
	}
	return 0;
}
int sec29(void){
	short q1[4][3][2] = {{1}, {2, 3}, {4, 5, 6}};
	short q2[4][3][2] = {1, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 4, 5, 6};
	short q3[4][3][2] = {{{1},}, {{2, 3},}, {{4, 5},{6},}};
	for (int i = 0; i < 4; i = i + 1){
		for (int j = 0; j < 3; j = j + 1){
			for (int k = 0; k < 2; k = k + 1){
				printf("q1[%d][%d][%d]=%d\n", i, j, k, (q1[i][j][k]));
				if (q1[i][j][k] != q2[i][j][k]) {
					return 1;
				}
				if (q2[i][j][k] != q3[i][j][k]) {
					return 1;
				}
			}
		}
	}
	return 0;
}
int sec31(void){
	typedef int A[];
	A a1 = {1, 2}, b1 = {3, 4, 5};
	int a2[] = {1, 2}, b2[] = {3, 4, 5};
	for (int i = 0; i < 2; i = i + 1){
		printf("a1[%d]=%d\n", i, a1[i]);
		if (a1[i] != a2[i]) { return 1; }
	}
	for (int i = 0; i < 3; i = i + 1){
		printf("b1[%d]=%d\n", i, b1[i]);
		if (b1[i] != b2[i]) { return 1; }
	}
	return 0;
}

int sec32(void){
	char s1[] = "abc", t1[3] = "abc";
	char s2[] = {'a', 'b', 'c', '\0'};
	char t2[] = {'a', 'b', 'c'};
	char* s3 = "abc";
	
	for (int i = 0; i < 4; i = i + 1){
		printf("s1[%d]=%d\n", i, s1[i]);
		if (s1[i] != s2[i]) { return 1; }
		if (s2[i] != s3[i]) { return 1; }
	}
	for (int i = 0; i < 3; i = i + 1){
		printf("t1[%d]=%d\n", i, t1[i]);
		if (t1[i] != t2[i]) { return 1; }
	}
	return 0;
}

int sec33(void){
	enum {member_one, member_two};
	char *nm[] = {
		[member_two] = "member two",
		[member_one] = "member one",
	};
	printf("%s\n", nm[0]);
	printf("%s\n", nm[1]);
	return 0;
}
int sec34(void){
	div_t x1 = {.quot = 2, .rem = -1};
	div_t x2 = {.rem = -1, .quot = 2};
	
	if (x1.quot != x2.quot) { return 1; }
	if (x1.rem != x2.rem) { return 1; }
	return 0;
}
int sec35(void){
	struct { int a[3], b;} w1[] = {[0].a = {1}, [1].a[0] = 2};
	struct { int a[3], b;} w2[2] = {0};
	w2[0].a[0] = 1; 
	w2[1].a[0] = 2;
	for (int i = 0; i < 2; i = i + 1){
		for (int j = 0; j < 3; j = j + 1){
			printf("w1[%d][%d]=%d\n", i, j, w1[i].a[j]);
			if (w1[i].a[j] != w2[i].a[j]) {return 1;}
		}
	}
	
	return 0;
}
#define MAX ((20))
int sec36(void){
	int a1[MAX] = {
		1, 3, 5, 7, 9, [MAX-5] = 8, 6, 4, 2, 0
	};
	int a2[20] = {
		1, 3, 5, 7, 9, 0, 0, 0, 0, 0, 
		0, 0, 0, 0, 0, 8, 6, 4, 2, 0
	};
	for (int i = 0; i < 20; i = i + 1){
		printf("a1[%d]=%d\n", i, a1[i]);
		if (a1[i] != a2[i]) {return 1;}
	}
	
	return 0;
}
int sec38(void){
	union {int a; float b; int c[2];} u1 = {.c = {1, 2}};
	union {int a; float b; int c[2];} u2 = {.a = 3};
	union {int a; float b; int c[2];} u3 = {.b = 4.5};
	
	if (u1.c[0] != 1) { return 1; }
	if (u1.c[1] != 2) { return 1; }
	if (u2.a != 3) { return 1; }
	if (u3.b != 4.5) { return 1; }
		
	return 0;
}

int main(void){
	if (sec26()) {return 26;}
	if (sec27()) {return 27;}
	if (sec28()) {return 28;}
	if (sec29()) {return 29;}
	if (sec31()) {return 31;}
	if (sec32()) {return 32;}
	if (sec33()) {return 33;}
	if (sec34()) {return 34;}
	if (sec35()) {return 35;}
	if (sec36()) {return 36;}
	if (sec38()) {return 38;}
	return 0;
}
