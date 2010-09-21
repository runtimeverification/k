struct t {int a[2];} s;
void f(struct t s) { s.a[1] = 3; }
void g(int a[2]) { printf("inner %p\n", a); a[1] = 5; }
int main() {
	int x = (f(s), s.a[1]);
	printf("%d\n", x);
	printf("outer %p\n", s.a); 
	int y = (g(s.a), s.a[1]);
	printf("%d\n", y);
	printf("%d\n", x + y);
	return x + y;
}
// should return 5, not 8
