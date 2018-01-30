// Testing new, constructor, method invocation.

class C {
  int i,j;
  void C(int x) {
    i = x;
    j = ++x;
  }
  void add(int d) {
    i = i+d;
    j = j-d;
  }
  void print2() {
    print(i, " ", j, "\n");
  }
}

class Main {
  int a,b;
  C o;
  void Main(){
    a = b = 5;
    o = new C(a);
    o.print2();
    o.add(++b);
    o.print2();
  }
}


// 5 6
// 11 0
