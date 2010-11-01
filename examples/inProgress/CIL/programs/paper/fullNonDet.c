typedef int (*funcptr)(int);

int a(int x, int y){ putchar('a'); return 0; }
int b(){ putchar('b'); return 0; }
int c(int x){ putchar('c'); return 0; }
int d(){ putchar('d'); return 0; }
int e(int x){ putchar('e'); return 0; }
funcptr f() { putchar('f'); return &e; }


int main() {
	int result = f()(a(b(), c(d())));
	return 0;
}
