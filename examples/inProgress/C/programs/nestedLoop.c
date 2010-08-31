#include <stdio.h>

int sec26(void){
	int y1[4][3] = {
		{1, 3, 5},
		{2, 4, 6},
		{3, 5, 7},
	};
	for (int i = 0; i < 4; i = i + 1){
		for (int j = 0; j < 3; j = j + 1){
			printf("(i, j)=(%d, %d)", i, j);
			if (y1[i][j] != y1[i][j]) {
				return 1;
			}
		}
	}
	return 0;
}
int main(void){
	if (sec26()) {return 26;}
	return 0;
}
