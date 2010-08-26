// baddef1.c: complain about inconsistent redef

struct S {
  int x;
  int y;
};

int size1() { return sizeof(struct S); }
