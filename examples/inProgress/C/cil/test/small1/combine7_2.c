struct list12 {
  struct list22 *realnext;
  struct list12 *next;
};

struct list22 {
  double       d;
  struct list22 *data;
};


int main() {
  struct list12 l;
}
