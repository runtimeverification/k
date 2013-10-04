// Program testing Collatz' conjecture up to a user-provided number.

class Main {
  int collatz(int n) {
    int s=0;
    while (n > 1) {
      s = s+1;
      if (n == (n/2)*2) { n = n/2; }
      else { n = 3*n+1; }
    }
    return s;
  }

  void Main() {
    print("Testing Collatz' conjecture up to what number? ");
    int m = read(), s;
    for (int i=1; i<=m; ++i) { 
      print("Testing Collatz' conjecture for n = ",i," ... ");
      s = collatz(i); 
      print("Done! It took ",s," steps.\n");
    }
    print("Done.  It appears to hold.\n");
  }
}
