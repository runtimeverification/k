


int main() {
  static void* array[] = { && L1, && L2, && L3 };
  int acc = 0;

 L1: acc += 1; goto * array[1];
 L2: acc += 2; goto * array[2];
 L3: acc += 3;

 return acc - 6;
}
