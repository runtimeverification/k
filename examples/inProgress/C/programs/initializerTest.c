int main(void) {
	struct s {
		int a;
		int b;
		struct q {
			int b;
			int c;
		} w;
		int x[2];
		int y;
		int z[];
	} s1 = {1, 2, .b =3, 4, 5, 6, 7};
	// if (s1.b != 2){
		// return 2;
	// }
	// int z = {2};
	return 0;
}
