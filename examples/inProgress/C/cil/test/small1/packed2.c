
//Tests for CIL's handling of the packed attribute

#define offsetof(t,f) ((unsigned long)&(((t *)0)->f))


//has size 6
struct s1 {
  short a;
  char b;
  short c;
} ;
//Duplicate array declarations force CIL (and gcc) to constant-fold and
//ensure sizeof(struct s1) equals 6:
extern int size6[6];
extern int size6[sizeof(struct s1)];

//has size 5
struct s2 {
  short a;
  char b;
  short c;
}  __attribute__((packed));
extern int size5[5];
extern int size5[sizeof(struct s2)];


extern int size1[1];
extern int size3[3];
extern int size4[4];
extern int size8[8];

//has size 8.  The packed prevents the 1 byte of padding from being added
//before b, but doesn't prevent the byte that is added afterwards.
struct s3 {
  char a;
  short b  __attribute__((packed));
  int c;
} s3;
extern int size8[sizeof(struct s3)];

//offsetof (struct s3).b == 1
extern int size1[offsetof(struct s3, b)];
//offsetof (struct s3).c == 4
extern int size4[offsetof(struct s3, c)];

//has size 6.  The first field has alignment 2, 
// so the whole struct has alignment 2.
struct s4 {
  short a;
  char b   __attribute__((packed));
  short c  __attribute__((packed));
};
extern int size6[sizeof(struct s4)];
extern int size3[offsetof(struct s4, c)];

//has size 5
struct s5 {
  short a ;
  char b   __attribute__((packed));
  short c  __attribute__((packed));
} __attribute__((packed));
extern int size5[sizeof(struct s5)];

//has size 7.  s1 has size 6, and the packed attribute here applies only to s6,
// not transitively to s1.
struct s6 {
  char a ;
  struct s1 s;
} __attribute__((packed));
extern int size7[7];
extern int size7[sizeof(struct s6)];


int main() {
  return 0;
}
