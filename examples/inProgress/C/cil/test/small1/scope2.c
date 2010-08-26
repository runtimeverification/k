
// Verify the coping for enum, struct union

typedef struct str {
  int x;
} STR;

int f1(STR *s1) {
  struct str {
    int y;
  } x;
  s1->x = x.y;
}

typedef struct { int g; } Z;

struct str glob1;

int f2() {
  struct str {
    int a;
  };
  while(1) {
    typedef struct str {
      int z;
    } Z;

    struct str a;
    glob1.x = ((Z*)&glob1)->z;
  }
}


Z globz;
int * globza = & globz.g;
