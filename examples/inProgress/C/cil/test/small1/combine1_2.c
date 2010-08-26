
typedef struct str1 {
  int random;
} FOO;

static int array[10];

int c2(void) {
  return sizeof(array) + sizeof(struct str1);
}
