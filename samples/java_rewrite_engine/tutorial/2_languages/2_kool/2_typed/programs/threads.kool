// Testing threads, making sure that the newly created threads share
// the object environment with their parent threads.  If that were not
// the case, then the newly created threads below would get stuck on
// looking up run(), as run is a member in their parent thread's object.

class Thread {
  void Thread() { }

  void run() { }  // you are supposed to override this method

  void start() {
    spawn { run(); };
  }
}


class Cell {
  int v;

  void Cell(int v) {
    this.v = v;
  }

  void inc() {
    ++v;
  }

}


class MyThread extends Thread {
  Cell c;

  void MyThread(Cell c) {
    this.c = c;
  }

  void run() {
    c.inc();
  }

}


class Main {

  void Main() {
    Cell c = new Cell(7);
    MyThread t1 = new MyThread(c);
    MyThread t2 = new MyThread(c);
    t1.start();
    t2.start();
    print(c.v,"\n");
  }

}

// 7, 8, or 9.  Use the "--search" option to see all three behaviors
