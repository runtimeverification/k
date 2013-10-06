// Testing cast
// This program should execute but should not type check                       

class A {
  int x;
  void A() {
    x=10;
  }
  int getA() {
    return x;
  }
}

class B extends A {
  int x;
  void B() {
    super.A();
    x=20;
  }
  int getB() {
    return x;
  }
}

class Main {
  void Main() {
    B b = new B();
    A a = (A) b;
    print("b.x = ", b.x, "\n");
    print("a.x = ", a.x, "\n");
    print("a.getB() = ", a.getB(), "\n");  // this should not type check.  why?
    print("a.getA() = ", a.getA(), "\n");
  }
}

// b.x = 20
// a.x = 10
// a.getB() = 20
// a.getA() = 10
