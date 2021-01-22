class Exception {
  int v;
  void Exception(int v) {
    print("Exception ", v, " thrown!\n");
    this.v = v;
  }
  int get() {
    return v;
  }
}

class Exception2 extends Exception {
  void Exception2(int v) {
    (Exception(v));  // Parentheses tell the parser this is not a type decl.
                     // Alternatively, use super.Exception or this.Exception.
                     // This is an artifact of our "too generous" grammar,
                     // allowing declarations like "int (v);". Java doesn't.
  }
}

class Main {

  void foo() {
    try {
      throw new Exception(5);
      print(17);                           // should not be printed
    } catch(Exception2 e) {
      throw new Exception2(e.get() + 2);   // should not be reached
    }
    throw new Exception(-1);               // should not be reached
  }


  void Main() {
    try {
      foo();
    } catch(Exception e) {
        print(e.get(),"\n");                 // should print 5
    }
  }

}

// 5
