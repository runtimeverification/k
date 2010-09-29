struct t {int a[2];} s;
void f(struct t s) { s.a[1] = 3; }
void g(int a[2]) { a[1] = 5; }
int main() {
	int x = (f(s), s.a[1]);
	int y = (g(s.a), s.a[1]);
	return x + y;
}
// should return 5, not 8
