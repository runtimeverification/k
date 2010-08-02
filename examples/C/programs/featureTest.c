int factorial(int n);
struct bitf {
	int a : 2;
	int b;
	struct bitf* pbitf;
	int c[3];
	int *d[4];
	int ***e;
	int f[2][5];
};

struct a {
	int x;
} * b;

int main() {
	struct bitf s;
	struct a y;
	s.a = 2;
	s.b = 18;
	int n = 10;
	int fact = factorial(n);
	int factorial = fact;

	return factorial;
}

int factorial(int n){
	if (n == 0 || n == 1) {
		return 1;
	}
	return n * factorial(n - 1);
}
