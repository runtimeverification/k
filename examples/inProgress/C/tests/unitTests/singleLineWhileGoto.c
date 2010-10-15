int main(void){
	int x = 5;
	goto crazy;
	while (0)
		crazy: x++;
		
	goto crazier;
	while (0)
		crazier: break;
		
	return x;
}
