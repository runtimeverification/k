unsigned long window_size = 0x10000;

unsigned test() {
	return (unsigned)window_size;
}

int main() {
	printf("%d\n", test());
	return 0;
}
