// PR3510 & rdar://6564697

struct ty { 
  int info;
  union {
    int id;
    char *str;
  } u;
} t1  = { 101,  1 };

struct ty2 { 
  float info __attribute__((packed));
  char x;
  int Y __attribute__((packed));
} __attribute__((packed)) t2  = { 101,  1, 204 };

struct ty3 { int A; char C[]; } t3 = { 4, "fo" };

struct ty4 { 
  long double x __attribute__((packed));
  char y;
  long double z __attribute__((packed));
} __attribute__((packed)) t4  = { 1.0,  4, 17.0 };


struct { 
  char x;
  unsigned char y : 4;
} __attribute__((packed)) t5a  = { 101,  15 };

struct { 
  char x;
  unsigned short y : 12;
} __attribute__((packed)) t5b  = { 101,  1231 };

struct { 
  char x;
  unsigned char y : 4;
  unsigned char z : 7;
} __attribute__((packed)) t5  = { 101,  15, 123 };


struct { 
  long double x;
  unsigned char y : 4;
} __attribute__((packed)) t6  = { 123.412,  5 };

struct { 
  char x;
  unsigned char y : 4;
  unsigned char q : 3;
  unsigned char z : 7;
} __attribute__((packed)) t7  = { 101,  15, 123 };


struct { 
  char x;
  unsigned short y : 4;
  unsigned short q : 12;
} __attribute__((packed)) t7a  = { 101,  15, 123 };

struct sDescrItem {
  char what;
  char *types;
  char type;
} t8 = {16, 0, 32};


struct resword {
  const int *a;
  unsigned b : 16;
  int c : 16;
} t9 = { 0, 123, 456 };

// rdar://6861719
#pragma pack(4)

struct t10s {
  short a;
  int *b;
};

#pragma pack()

int x = 42;
struct t10s t10 = { 
.b = &x
};


#include <stdio.h>

int main() {
  printf("1: %d, %d\n", t1.info, t1.u.id);
  printf("2: %f, %d, %d\n", t2.info, t2.x, t2.Y);
  printf("3: %d %s\n", t3.A, t3.C);
  printf("4: %f %d %f\n", (double)t4.x, t4.y, (double)t4.z);
  printf("5: %d %d %d\n", t5.x, t5.y, t5.z);
  printf("5a: %d %d\n", t5a.x, t5a.y);
  printf("5b: %d %d\n", t5b.x, t5b.y);
  printf("6: %Lf %d\n", t6.x, t6.y);
  printf("7: %d %d %d %d\n", t7.x, t7.y, t7.q, t7.z);
  printf("7a: %d %d %d\n", t7a.x, t7a.y, t7a.q);
  printf("8: %d %d\n", t8.what, t8.type);
  printf("9: %d %d\n", t9.b, t9.c);
  printf("10: %d\n", *t10.b);
  return 0;
}
