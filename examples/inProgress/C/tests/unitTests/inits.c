#include <stdio.h> 

int main(void) {
	int x[] = {1,3,5};
	int y0[] = {1,3,5,2,4,6,3,5,7,0,0,0};
	int y1[4][3] = {
		{1,3,5},
		{2,4,6},
		{3,5,7},
	};
	int y2[4][3] = {1,3,5,2,4,6,3,5,7};
	int y3[4][3] = {
		{1},{2},{3},{4}
	};

	/* y0, y1, and y2, as declared, should define and 
	initialize identical arrays. */
	for(int i=0; i<4; i++) {
		for(int j=0; j<3; j++){
			int k = 3*i+j;
			if( y1[i][j] != y2[i][j] || y1[i][j] != y0[k]) {
				printf("i=%d, j=%d, k=%d; y0[k]=%d, y1[i][j]=%d, y2[i][j]=%d\n", 
					i, j, k, y0[k], y1[i][j], y2[i][j]
				);
			}
		}
	}
	return 0;
}
