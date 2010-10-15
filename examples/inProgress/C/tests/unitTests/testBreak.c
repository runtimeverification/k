int main(void){
	int i = 5;
	int retval = 0;
	while (i > 0) {
		i--;
		retval++;
		if (i == 3) {
			break;
		}
	}
	return retval;
}
