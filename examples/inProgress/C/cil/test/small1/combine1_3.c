typedef int INT, *PINT;

struct str1 {
  INT x1;
  int x2;
} array2;

int c3(void) {
  int var;

  var = 9; /*  Hopefully we do not overwrite the global one */
  return sizeof(array2);
}
