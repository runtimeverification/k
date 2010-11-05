extern void printf(char *, ...);
#define E(n) { printf("Error %d\n", n); return n; }

// from linux sources
int tickadj1 = 500/ 100  ? : 1;
int tickadj2 = 0 / 100 ? : 1;

int main() {
  if(tickadj1 != 5) E(1);
  if(tickadj2 != 1) E(2);

  return 0;
}
