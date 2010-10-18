int main(void){
	int x = 0;
	int i = 0;
	switch (4) {
		case 4: do {i++; x++; int x = 5; case 5: x++;} while (i < 3);
	}
	switch (2) {
		case 2: x *= 2;
		case 4: do {x++; int x = 5; case 5: x++;} while (0);
	}
	return x;
}
