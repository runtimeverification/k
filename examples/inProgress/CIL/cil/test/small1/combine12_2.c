struct bar {
  struct {
    int x;
    struct foo *next;
  } c;
};

struct baz {
  struct {
    int x;
    struct bar *next;
  } b;
} g;
