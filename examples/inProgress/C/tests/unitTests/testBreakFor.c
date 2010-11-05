int main(void){
	int retval = 0;
	for (int i = 0; i < 10; i++){
		retval++;
		if (i == 4) { break; }
	}
	return retval;
}
