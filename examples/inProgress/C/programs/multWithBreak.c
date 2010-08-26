int main() {
	int product1 = 1;
	int product2 = 1;
	int arr1[] = {1, 2, 3, 0, 4, 5} ;
	int arr2[] = {1, 2, 3, 4, 5} ;
	
	for(int i = 0; i < 6; i++){
		product1 *= arr1[i];
		if (product1 == 0){
			break;
		}
	}
	
	for(int i = 0; i < 5; i++){
		product2 *= arr2[i];
	}
	
	return product1 + product2;
}
