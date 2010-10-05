// this comes from the cq test suite
int array(int a[], int size, int start){
	int i;
	for(i = 0; i < size; i++) {
		if(a[i] != i + start) return 1;
	}

	return 0;
}

int main(void){
	int x3d[3][5][7];
	for (int i=0; i<3; i++)
		for (int j=0; j<5; j++)
			for (int k=0; k<7; k++)
				x3d[i][j][k] = i*35+j*7+k;
	int i = 1;
	int j = 2;
	int k = 3;
	
	if (array(x3d, 105, 0)) {
		printf("Bug1\n");
	}
	if (array(x3d[i], 35, 35)) {
		printf("Bug2\n");
	}
	if (array(x3d[i][j], 7, 49)) {
		printf("Bug3\n");
	} 
	if (x3d[i][j][k] - 52) {
		printf("Bug4\n");
	}
	return 0;
}
