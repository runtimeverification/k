
struct stralloc {
   char *s ;
   unsigned int len ;
   unsigned int a ;
};

static struct stralloc tmp; // This will turn into tmp___0 (merger)


int main() {
  int tmp___0 = 5; // This will stay as it is, thus conflicting with the
                   // new global
  char *path = tmp.s; // This will be changed to tmp___0.s !!!
  return 0;
}
