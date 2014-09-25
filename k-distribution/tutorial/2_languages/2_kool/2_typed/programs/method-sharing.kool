// This program shows how method closures can be returned by other
// methods, bound to local variables, and then invoked.

class A {
  int c;
  void A() {
    c = 0;
  }
  void inc() {
    ++c;
  }
}

class B {
  A a = new A();
  void->void m = a.inc;
  int x = 0;
  void B() {
    print(a.c, " ");
    m();
    print(a.c, " ");
  }
  void->void getM() {
    return m;
  }
}

class Main {
  void->void f;
  void Main() {
    B b = new B();
    void->void t = f = b.getM();
    f();
    print(b.a.c, " ");
    t();
    print(b.a.c, " ");
    (b.getM())();                 // shows the higher-order aspect of KOOL
    print(b.a.c, "\n");
  }
}

// 0 1 2 3 4
