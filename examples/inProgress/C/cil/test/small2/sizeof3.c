//Bug caused by overflow in bitsSizeOf (SourceForge #1641570)

//Partial workaround:  define "bytesSizeOf", not bitsSizeOf, to give us 8x more
//breathing room.
//Better workaround: make bitsSizeOf return an int64
//Current solution: a warning

char tab[300000000]; // three hundred million times 8 bits = -947483648 mod 2**31

//TODO: give somthing better than a warning here ...
extern char foo[sizeof(tab)]; //KEEP folding: error = Unable to do constant-folding

char foo[300000000];

int main () {
  int i;

  tab[999999999] = foo[5];
  i = sizeof (tab);

  return 0;
}
