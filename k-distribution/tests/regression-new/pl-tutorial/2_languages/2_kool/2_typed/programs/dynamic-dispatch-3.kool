// This program illustrates that if a method of type t1 -> t2 is
// overridden with one of type t1' -> t2', then it should be the case
// that t2' is a subtype of t2 and that t1 is a subtype of t1'.  This is
// consistent with the type ordering over function types, namely:
//
//   t1 -> t2 >= t1' -> t2'    iff    t1 <= t1' and t2 >= t2'
//
// We say that function types are co-variant with their codomains and are
// contra-variant with their domains.  A simple way to remember this is
// that constants are particular functions (with no arguments), so the
// function and its codomain must vary the same way.

class A {
  int x;
  void A() {
    x = 1;
  }
  B m1(B b) {
    b.y = 10;
    return b;
  }
}

class B extends A {
  int y;
  void B() {
    super.A();
    y = 100;
  }
  B m2(B b) {
    return m1(b);   // HOT-SPOT
// If m1 gets overridden in an extension of B, then the following must hold:
// (1) The new m1 should not get stuck when called above, so B must be
// a subtype of its new argument's type.
// (2) The type of the value returned by the new m1 should be a subtype
// of B, so it can serve as a value returned by m2().
// Hence, if we override m1 into one of type C1 -> C2, then it should be
// the case that C1 <= B and B >= C2.  This is precisely what we do next.
  }
}

class C extends B {
  int z;
  void C() {
    super.B();
    z = 1000;
  }
  C m1(A a) {
    z = a.x;
    return this;
  }
// To see how the program gets stuck under dynamic type checking, you
// can do the following changes on the method m1 above:
// (1) Change the class of its argument into C.  Then the
// program will get stuck trying to show, at the HOT-SPOT, that the type
// B of b is a subtype of the new C.  Or
// (2) Change the class of its result into A, and return
// "new A()" instead of "this".  Then the program will get stuck
// trying to show that the returned value at HOT-SPOT, of type A,
// has the expected return type of m2, namely B.
// The static semantics should also catch these errors (even when you
// don't return "new A()" instead of "this").
}

class Main {
  void Main() {
    A a = new A();
    B b = new B();
    C c = new C();
    print(b.y, " ", c.z, "\n");
    print((b.m2(b)).y, " ", (c.m2(b)).y, "\n");
    print(b.y, " ", c.z, "\n");
  }
}
