
#define X 5
int foo(int x) {
  int y = ((1UL << 12) / (6 * 64) * 64 * 8 > 1024 * 1024
           ? 1024 * 1024
           : (1UL << 12) / (6 * 64) * 64 * 8)
          / (8 *  sizeof(unsigned long int));
  if(5 > 7 ? 1 + sizeof(char) : 5 << 2) {
    x ++;
  } else {
    x --;
  }
}
