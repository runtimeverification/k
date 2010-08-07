#include <stdio.h>
int factorial(int n);

struct bitf {
	int a : 3;			// 3/8
	int b;				// 04
	struct bitf* pbitf;	// 08
	int c[3];			// 12
	int *d[4];			// 08
	int ***e;			// 08
	int f[2][5];		// 10
};

struct a {
	int x;
} * b;

int main() {
	int arr[] = L"Hello";
	printf("&arr=\t%p\n", &arr);
	printf("arr=\t%p\n", arr);
	printf("hello=\t%p\n", "Hello");
	printf("len(arr)=\t%d\n", sizeof(arr)/sizeof(arr[0]));

	struct bitf s;
	struct a y;
	struct b {
		int q;
	} x;
	struct b z;
	s.a = 1;
	s.b = 18;
	int n = 10;
	int fact = factorial(n);
	int factorial = fact;

	return factorial;
}

// this isn't being scoped properly
int blah (struct zed {int a; int b; int c : 4;} c){
	return c.a;
}

int factorial(int n){
	struct b {
		int y;
		int x;
	} x;
	if (n == 0 || n == 1) {
		return 1;
	}
	return n * factorial(n - 1);
}
