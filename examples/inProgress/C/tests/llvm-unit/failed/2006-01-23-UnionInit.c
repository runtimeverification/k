#include <stdio.h>

//===- PR156 --------------------------------------------------------------===//
struct task_struct {
  char comm[16];
};
union task_union {
  struct task_struct task;
  unsigned long stack[2048*sizeof(long)/sizeof(long)];
};
union task_union init_task_union = { { comm: "swapper" } };

//===- PR295/PR568 --------------------------------------------------------===//

struct inflate_huft_s {
  union {
    struct {
      unsigned char Exop;
      unsigned char Bits;
    } what;
    unsigned pad;
  } word;
  unsigned base;
} fixed_tl[] = {
  {{{96,7}},256}
};

//===- PR574 --------------------------------------------------------------===//

union bt4 {
  struct at4 {
    unsigned long int av4;
  } gv4;
  double hv4;
} bkv4 = { { 61172160UL } };

struct bt1 {
  signed dv1:4;
  signed ev1:6;
  unsigned char fv1[1];
} cav1 = { 4, 22, { '\x2' } };

//===- PR162 --------------------------------------------------------------===//

union foo {
  struct { char A, B; } X;
  int C;
} V = { {1, 2} };

//===- PR650 --------------------------------------------------------------===//

union nameData {
  char data[64];
  int alignmentDummy;
} nd = {"relname"};

//===- PR199 --------------------------------------------------------------===//

struct one {
  int a;
  int values[];
} hobbit = {5, {1, 2, 3}};

extern struct one hobbit2;   // resize after first use seen
void *foo() { return &hobbit2; }
struct one hobbit2 = {5, {1, 2, 3}};

//===- PR431 --------------------------------------------------------------===//

struct {
  int x;
  int v[];
} data = {0, {1,2,3} };

//===- PR654 --------------------------------------------------------------===//

struct {
  char *inplace;
  char chunk_data[];
} s = {0, "   xyzkasjdlf     "};

//===- PR323 --------------------------------------------------------------===//

struct dvd_send_key {
  unsigned agid : 2;
  unsigned char key[5];
};

union {
  struct dvd_send_key lsk;
} ai = {{3, "foo"}};

//===- PR627 --------------------------------------------------------------===//

typedef struct {} emptystruct;
typedef struct {
  emptystruct raw_lock;
} spinlock_t;

emptystruct one_raw_spinlock (void) {
  emptystruct raw;
  printf("returning raw_lock\n");
  return raw;
}

//===- PR684 --------------------------------------------------------------===//

union ucast {
  int i;
  struct s {
    int i1, i2, i3;
  } s;
};
union ucast ucast_test (void) {
  struct s y = {1, 2};
  union ucast z = (union ucast)y;
  return z;
}


//===- rdar://6828787 -----------------------------------------------------===//

#pragma pack(4)

struct foo2 {
  short a;
  long  x;
  short y;
};

#pragma pack()

struct foo2 foo2 = { 23122, -12312731, -312 };


//===- Checker ------------------------------------------------------------===//

int main() {
  union ucast XX;
  spinlock_t lock;
  printf("PR156: %s\n", init_task_union.task.comm);
  printf("PR295/PR568: %d, %d\n", fixed_tl[0].word.pad, fixed_tl[0].base);
  printf("PR574: %d, %d, %d, %d\n", (int)bkv4.gv4.av4, cav1.dv1, cav1.ev1,
         cav1.fv1[0]);
  printf("PR162: %d, %d, %d\n", V.X.A, V.X.B, V.C);
  printf("PR650: %s, %d\n", nd.data, nd.alignmentDummy);
  printf("PR199: %d, %d, %d, %d\n", hobbit.a, hobbit.values[0], 
         hobbit.values[1], hobbit.values[2]);
  printf("PR199: %d, %d, %d, %d\n", hobbit2.a, hobbit2.values[0], 
         hobbit2.values[1], hobbit2.values[2]);
  printf("PR431: %d, %d, %d, %d\n", data.x, data.v[0], 
         data.v[1], data.v[2]);
  printf("PR654: %ld, '%s'\n", (long) s.inplace, s.chunk_data);
  printf("PR323: %d, '%s'\n", ai.lsk.agid, ai.lsk.key);
  lock = (spinlock_t) { .raw_lock = one_raw_spinlock() };
  printf("PR627: %d\n", (int)sizeof(lock));
  XX = ucast_test();
  printf("PR684: %d, %d, %d %d\n", XX.s.i1, XX.s.i2, XX.s.i3, XX.i);
  printf("rdar://6828787: %d, %d, %d\n", foo2.a, (int)foo2.x, foo2.y);
  return 0;
}
