// Testing mutually recursive uses of this.method

class OddEven {
  int n;
  void OddEven(int x) {
    n = x;
  }
  int even() {
    if (n == 0) {
      return 1;
    }
    else {
      n = n - 1;
      return this.odd();
    }
  }
  int odd() {
    if (n == 0) {
      return 0;
    }
    else {
      n = n - 1;
      return this.even();
    }
  }
}

class Main {
  void Main() {
    print((new OddEven(17)).odd(), "\n");
  }
}

// 1
