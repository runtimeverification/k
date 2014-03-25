class X { void X() {} }
class Y extends X { void Y() {} }
class Z extends X { void Z() {} }

class Main {
  void Main() {
    X x  = new X();
    Y y  = new Y();
    Z z  = new Z();
    X xy = new Y();     // ok (y is subclass of X)
    X xz = new Z();     // ok (Z is subclass of X)
//  Y yz = new Z();     // incompatible types
//  Y y1 = new X();     // X is not a Y
//  Z z1 = new X();     // X is not a Z
    X x1 = y;           // ok (y is subclass of X)
    X x2 = z;           // ok (z is subclass of X)
//  Y y1 = (Y) x;       // types ok but produces runtime error
//  Z z1 = (Z) x;       // types ok but produces runtime error
    Y y2 = (Y) x1;      // types and runs ok (x1 is type Y)
    Z z2 = (Z) x2;      // types and runs ok (x2 is type Z)
//  Y y3 = (Y) z;       // inconvertible types
//  Z z3 = (Z) y;       // inconvertible types
    Object o = z;
//  Object o1 = (Y) o;  // types ok but produces runtime error
    print("OK\n");
  }
}
