#include "helpers.h"

union Array {
  v8sd  Vectors[100];
  double Floats[800];
};

union Array TheArray;

int main() {
  int i;
  v8sd sum = { 0, 0, 0, 0, 0, 0, 0, 0};
  D8V sumV;
  for (i = 0; i < 800; ++i)
    TheArray.Floats[i] = i*12.345;

  for (i = 0; i < 100; ++i)
    sum += TheArray.Vectors[i];

  sumV.V = sum;
  printD8V(&sumV);
  return 0;
}
