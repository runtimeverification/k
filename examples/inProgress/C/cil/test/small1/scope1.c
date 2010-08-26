extern void exit(int);

int foo[5];

enum foo {
  l1 = 0,
  l2, l3
};


typedef struct Person {
  char *name;
} Person;



int main() {
  int l, *l2 = & l;
  extern int globint;
  Person *Person = 0;
  {
    int * l1 = l2;
    *l1 = *l2 + l3;
    globint = 2;
  }
  {
    extern int globint;
    void increm(int *);
    enum {
      l1 = 7,
      l2 = 9,
    } z;
    increm(& globint);
    return ((l1 + l2 + l3) - 18) + (globint - 3);
  }
  *l2 = l3 + l1;
  exit(1);
}

void increm(int *i) {
  (*i) ++;
}

int globint;
