
struct two {
  int i_1;
  int i_2;
};

struct nosplit {
  // Don't split this struct.  
  // (Or if you do, handle the array assignment correctly.)
  int i_5;
  int i_6[10];
};

struct three {
  int i_0;
  struct two i_1and2;
  struct nosplit i_56;
};

struct three global = { 0, {10, 20}};
//Try an external declaration:
extern struct three bar(struct three arg);
extern void barvoid(struct three arg);

extern struct three externstruct; //not split

int main() {
  struct three local1 = externstruct;
  struct three local2 = externstruct;
  struct three local3 = local2;

  barvoid(local1);      //local1 is split
  local3 = bar(local2); //local2 is not split, but the args to bar are

  barvoid(global);      //global is not split, but the args to barvoid are

  externstruct = bar(externstruct);

  
  return 0;
}
