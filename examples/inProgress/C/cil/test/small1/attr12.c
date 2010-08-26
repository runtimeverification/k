
//Openssh 4.3p2 uses an empty attribute:
int strnvis(char *, const char *, unsigned int, int)  __attribute__ (());

int main() {
  strnvis(0,0,0,0);
}
