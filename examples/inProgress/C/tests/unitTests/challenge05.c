struct t {int x;} s;
struct t f(struct t s) {
	s.x = 5;
	return s;
}
int main() {
	struct t (*fp)(struct t) = f;
	return fp(s).x + s.x;
}
// should return 5, not 0 or 10
