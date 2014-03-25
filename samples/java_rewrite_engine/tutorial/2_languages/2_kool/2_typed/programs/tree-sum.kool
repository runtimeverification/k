// Building and traversing a tree.

class Summable {      // Class Summable is not needed in dynamically typed KOOL
  void Summable() {}  // Needed in statically typed KOOL; moreover, it needs
  int sum() {}        // to be consistently typed in extensions.
}

class Node extends Summable {
  Summable left, right;
  void Node(Summable left, Summable right) {
    this.left = left;
    this.right = right;
  }
  int sum() {
    return (left.sum() + right.sum());
  }
}

class Leaf extends Summable {
  int val;
  void Leaf(int val) {
    this.val = val;
  }
  int sum() {
    return val;
  }
}

class Main {
  void Main() {
    Node o;
    o = new Node(new Node(new Leaf(3), new Leaf(4)), new Leaf(5));
    print(o.sum(), "\n");
  }
}

// 12
