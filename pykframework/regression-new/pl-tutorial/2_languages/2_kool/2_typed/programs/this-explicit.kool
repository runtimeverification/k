// Testing the explicit use of "this"

class C {
  void C() {}
  int m1() {
    return this.m2();
  }
  int m2() {
    return 13;
  }
}

class Main {
  void Main() {
    print((new C()).m1(), "\n");
  }
}

// 13
