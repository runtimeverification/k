// Testing super in combination with dynamic method dispatch

class A {
  int i;
  int j;
  int A() {
    i = 1;
    j = i + 1;
    return j;
  }
  int f() {
    return A();
  }
  int g() {
    return f();
  }
  int h() {
    return (i + j);
  }
}

class B extends A {
  int j;
  int k;
  int A() {
    return this.B();
  }
  int B() {
    super.A();
    j = 10;
    k = j + 1;
    return k;
  }
  int g() {
    return super.h();
  }
  int h() {
    return g();	   
  }
}

class C extends B {
  int A() {
    return super.A();
  }
  int B() {
    return super.B();
  }
  int C() {
    i = 100;
    j = i + 1;
    k = j + 1;
    return k;
  }
  int g() {
    return (i + k * j);
  }
}

class Main {
  void p(A o) {
    print(o.f(), " ");
    print(o.g(), " ");
    print(o.h(), "\n");
  }
  void Main() {
    this.p(new A());
    this.p(new B());
    this.p(new C());
  }
}

// 2 2 3
// 11 3 3
// 11 111 111
