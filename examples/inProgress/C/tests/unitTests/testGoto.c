int test1(void){
	int x = 0;
	goto test1a;
	x = 5;
	test1a:
	return x;
}

int test2(void){
	int x = 0;
	goto test2a;
	{
		x = 5;
		int y;
		test2a:
		y = 5;
		return 2 * (y == x);
	}
	return 2;
}

int test3(void){
	int x = 2;
	goto test3a;
	int y = 0;
	test3a:
	y = 2;
	return y - x;
}

int test4(void){
	int x = 0;
	{// 1
		int y = 1;
		{ // 2
			int w = 0;
			goto test4a;
		}
		int z = 5;
		{ // 2
			{ // 3
				test4a:
				z = 5;
				return 4 * ((z - y) != 4);
			}
		}
	}
	
	return 4;
}

int main(void){
	if (test1()) return 1;
	if (test2()) return 2;
	if (test3()) return 3;
	if (test4()) return 4;
	return 0;
}
