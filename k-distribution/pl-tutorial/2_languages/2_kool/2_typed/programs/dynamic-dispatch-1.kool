// Testing dynamic method dispatch

class C1 {
  void C1() {}
  int m1() { return 1; }
  int m2() { return m1(); }
}

class C2 extends C1 {
  void C2() {}
  int m1() { return 2; }
}

class Main {
  void Main() {
    C1 o1 = new C1();
    C2 o2 = new C2();
    print(o1.m1(), " ", o1.m2(), " ", o2.m1(), " ", o2.m2(), "\n");
  }
}

// 1 1 2 2 
