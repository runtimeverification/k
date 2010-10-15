int main(void){
	int x = 5;
	
	while (1) {
		goto breakme;
		x++;
		breakme:
		break;
	}
	
	return x;
}
