int main(void){
	int x = 5;
	goto crazy;
	if (0)
		crazy: x++;
	return x;
}
