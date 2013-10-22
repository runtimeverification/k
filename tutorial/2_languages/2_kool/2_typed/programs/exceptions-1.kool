// This program tests the basic functionality of exceptions

class Main {

  void foo() {
    try {
      throw 5;
      print(17);      // should not be printed
    }
    catch(int e) {
      throw e + 2;    // throws 7
    }
    throw 1;          // should not be reached
  }

  void Main() {
    try {
      foo();
    }
    catch(int e) {
      print(e,"\n");  // should print 7
    }
  }

}

// 7
