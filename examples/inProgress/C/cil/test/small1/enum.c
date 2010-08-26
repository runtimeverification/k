
typedef enum foo {
  F1 = 0,
  F2 = (long int)(~0UL >> 1),
  F3,
  F4
} ENUM;



void foo(void) {
  int x = F2;
  int y = F1;
}
