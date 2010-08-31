int main(void) {
	int a[3][2];
	a[0][0] = 5;
	a[0][1] = 6;
	a[1][0] = 7;
	a[1][1] = 8;
	a[2][0] = 9;
	a[2][1] = 10;
	
	if (a[0][0] != 5) { return 5; }
	if (a[0][1] != 6) { return 6; }
	if (a[1][0] != 7) { return 7; }
	if (a[1][1] != 8) { return 8; }
	if (a[2][0] != 9) { return 9; }
	if (a[2][1] != 10) { return 10; }
	
	return 0;
}
