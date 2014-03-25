// This program tests the subtyping of function types

class A {
  void A() {}
}

class B extends A {
  void B() {}
}

class C extends B {
  void C() {}
  A AA(A a) {}
  B AB(A a) {}
  C AC(A a) {}
  A BA(B b) {}
  B BB(B b) {}
  C BC(B b) {}
  A CA(C c) {}
  B CB(C c) {}
  C CC(C c) {}
}

class Main extends C {
  void Main() {
  C c = new C();
  A->A aa = c.AA;
  A->B ab = c.AB;
  A->C ac = c.AC;
  B->A ba = c.BA;
  B->B bb = c.BB;
  B->C bc = c.BC;
  C->A ca = c.CA;
  C->B cb = c.CB;
  C->C cc = c.CC;
  ca = ba = aa = ab = ac; // OK: C->A > B->A > A->A > A->B > A->C
  ca = cb = cc = bc = ac; // OK: C->A > C->B > C->C > B->C > A->C
  ba = bb = ab;           // OK: B->A > B->B > A->B
  cb = bb = bc;           // OK: C->B > B->B > B->C
  print("OK\n");
//  ac = bc;  print("Wrong! A->C < B->C\n");
//  bb = cc;  print("Wrong! Incompatible types.\n");
  print("Done\n");
  }
}
