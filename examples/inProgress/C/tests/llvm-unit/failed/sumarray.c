#include "helpers.h"

union Array {
  v4sf  Vectors[100];
  float Floats [400];
};

union Array TheArray;

int main() {
  int i;
  v4sf sum = { 0, 0, 0, 0};
  FV sumFV;
  for (i = 0; i < 400; ++i)
    TheArray.Floats[i] = i*12.345F;

  for (i = 0; i < 100; ++i)
    sum += TheArray.Vectors[i];

  sumFV.V = sum;
  printFV(&sumFV);
  return 0;
}
