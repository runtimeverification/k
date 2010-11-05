extern void exit(int);
extern void abort(void);


// Fron ctorture
typedef enum foo E;
enum foo { e0,
           e1 = e0 + 2 };

enum bar { b0 = e1 };
  
struct {
  E eval;
  enum bar b;
} s;

void p() {
  abort();
}

void f() {
  switch (s.eval) {
  case e0:
  case e1 + 2:
    p();
  }
}

int main() {
  s.eval = e1;
  f();
  exit(0);
}
