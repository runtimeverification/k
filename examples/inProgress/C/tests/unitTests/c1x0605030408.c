#include <stddef.h>
size_t fsize3(int n) {
	char b[n + 3];
	return sizeof b;
}
int main(void) {
	size_t size;
	size = fsize3(10);
	return size;
}
