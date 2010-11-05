// structattr.c
// testing some placement of 'attribute' w.r.t. 'struct' etc.

struct A {
  int x;
} __attribute__((packed));
struct A a;

struct B {
  int x;
} __attribute__((packed)) b;

#if 1
// this is allowed by gcc, but I don't want to implement it because
// it means somehow merging all the attributes across all the
// forward decls and the defn ...
//struct __attribute__((packed)) C;

struct __attribute__((packed)) C {
  int x;
};
struct C c;

struct __attribute__((packed)) D {
  int x;
} d;
#endif // 0/1

// not allowed
//  struct E __attribute__((packed)) {
//    int x;
//  };

// 8/31/03: also need it to work with anonymous structs
struct __attribute__((__packed__)) {
    int i;
    char c;
} e;


typedef unsigned long ULONG;
typedef int WCHAR;
typedef struct __attribute__((packed, aligned(4))) _INFORMATION {
     ULONG FileAttributes;
     ULONG FileNameLength;
     WCHAR FileName[1];
} INFORMATION, *PINFORMATION;

INFORMATION i;
PINFORMATION pi;

int main()
{
  return 0;
}
