struct t {int x;} s;
struct t f(struct t s) {
	s.x = 5;
	return s;
}
int main() {
	return f(s).x + s.x;
}
// should return 5, not 0 or 10
