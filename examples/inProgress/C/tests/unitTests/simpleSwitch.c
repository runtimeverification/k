int main(void){
	int x = 5;
	int retval = 0;
	switch (x) {
		case 4: break;
		case 5: retval++;
		case 6: 
			retval++;
			break;
		default: retval++;
	}
	
	switch(x)
		case 5: retval *= 2;
		
	switch(x) {
		case 4: retval *= 2; break;
		default : retval *= 3;
		case 6 : retval *= 5;
	}
		
	return retval;
}
