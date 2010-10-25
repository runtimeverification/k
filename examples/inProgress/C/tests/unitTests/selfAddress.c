int main(void){
	struct s {struct s* p;} myS = {&myS};
	return 0;
}
