// Testing field shadowing and super.

class C1 {
  int x, y;
  void C1() {
    x=1;
    y=2;
  }
}

class C2 extends C1 {
  int y, z;
  void C2() {
    C1();
    y=20;
    z=super.y;
  }
}

class C3 extends C2 {
  int x, y, z, u, w;
  void C3() {
    C2();
    x=100;
    y=200;
    z=super.x;
    u=super.y;
    w=super.z;
  }
}

class Main {
  void Main() {
    C3 o = new C3();
    print(o.x, " ", o.y, " ", o.z, " ", o.u, " ", o.w, "\n");
  }
}

// 100 200 1 20 2
