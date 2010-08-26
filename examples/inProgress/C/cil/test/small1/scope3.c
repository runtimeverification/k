

struct def *bar(); // Forward declaration


typedef int INT;
enum lateenum {
  FOO, BAR
};

typedef struct def {
  int f1;
} *defnamed;

void foo() {
  bar(BAR, 5);
}

defnamed bar(enum lateenum x1, INT x2);
