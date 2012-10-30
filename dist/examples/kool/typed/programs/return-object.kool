// Test returning objects in methods and then invoking methods on them

class C {
  int val;
  void C(int v) {
    val = v;
  }
  G m1() {
    return (new G(val + 9));
  }
}

class G {
  int a;
  void G(int t) {
    a = t;
  }
  void print2() { print(a, "\n"); }
}

class Main {
  void Main() {
    ((new C(1)).m1()).print2();
  }
}

// 10


