#include <stdio.h>

int sec26(void){
	int y1[4][3] = {
		{1, 3, 5},
		{2, 4, 6},
		{3, 5, 7},
	};
	int y2[4][3] = {1, 3, 5, 2, 4, 6, 3, 5, 7};
	for (int i = 0; i < 4; i = i + 1){
		for (int j = 0; j < 3; j = j + 1){
			printf("y1[%d][%d]=%d, y2[%d][%d]=%d\n", i, j, ((int*)y1)[i * 3 + j], i, j, ((int*)y2)[i * 3 + j]);
			if (y1[i][j] != y2[i][j]) {
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
