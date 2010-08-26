//Some uses of attributes in initramfs.c in the 2.6 linux kernel:

//The attribute should go on the variables, not the enum type.
static __attribute__ ((__section__ (".init.data"))) enum state {
 Start,
 Collect,
 GotHeader,
 SkipIt,
 GotName,
 CopyFile,
 GotSymlink,
 Reset
} state, next_state;




//This attribute belongs to the function, not the return type:
int __attribute__((noinline)) inflate_fixed(void){
  return 0;
}


int main() {
  state = Reset;
  return 0;
}

///////////////////////////////////////////////////////////////////////////

//More tests of the section attribute:  (not in initramfs.c)
__attribute__ ((__section__ (".init.data"))) enum state state2;
enum state __attribute__ ((__section__ (".init.data"))) state3;

__attribute__ ((__section__ (".init.data"))) struct foo {
  int field;
} mystruct;

static __attribute__ ((__section__ (".init.data"))) union {
  int field;
} myunion;


int test() {
  state2 = state3 = Reset;
  myunion.field = 15;
  return 0;
}

