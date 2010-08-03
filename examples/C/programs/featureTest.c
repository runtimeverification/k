int factorial(int n);
struct bitf {
	int a : 2;			// 2/8
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
	struct bitf s;
	struct a y;
	struct b {
		int q;
	} x;
	struct b z;
	// s.a = 2;
	// s.b = 18;
	int n = 10;
	int fact = factorial(n);
	int factorial = fact;

	return factorial;
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
