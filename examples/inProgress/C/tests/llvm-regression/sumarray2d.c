#include <stdio.h>
#define DIMEN 10
int SumArray(int Array[][DIMEN], unsigned int NumI, unsigned int NumJ) {
  unsigned i, j;
  int Result = 0;
  
  for (i = 0; i < NumI; i++)
    for (j = 0; j < NumJ; j++)
      Result += Array[i][j];
  
  return Result;
}

int main() {
  int Array[DIMEN][DIMEN];
  unsigned int i, j;
  
  for (i = 0; i < DIMEN; i++)
    Array[i][i] = -i;
  
  for (i = 0; i < DIMEN; i++)
    for (j = 0; j < DIMEN; j++)
      if (j != i)
        Array[i][j] = i+j;
  
  printf("Sum(Array[%d,%d] = %d\n", DIMEN, DIMEN, SumArray(Array, DIMEN, DIMEN));
  
  return 0;
}
