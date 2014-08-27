// Testing local variable shadowing a field

class C {
  int f;
  void C(int v) {
    f = v;
  }
  int get() { return f; }
}

class G {
  C o;
  void G(C o) {
    this.o = o;
  }
  int d() {
    int f = 9;
    return (o.get());
  }
}

class Main {
  void Main() {
    C t = new C(1);
    G y = new G(t);
    print(y.d(), "\n");
  }
}

// 1
