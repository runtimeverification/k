int factorial(int n);

int main() {
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
