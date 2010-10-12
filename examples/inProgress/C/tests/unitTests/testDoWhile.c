int main(void){
	int i = 5;
	int x = 0;
	do {
		i--;
		x++;
	} while (i > 0);
	
	do {
		x++;
	} while (0);
	
	return x;
}
