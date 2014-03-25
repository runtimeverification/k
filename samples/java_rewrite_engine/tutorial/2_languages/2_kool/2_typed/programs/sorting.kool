// This program defines a class Sorting which includes several sorting
// algorithms.  It also illustrates how method closures can be stored
// in an array and then executed one by one (see method map in main).

class Sorting {
  int[] array;
  int size;

  void Sorting(int n) {
    int x[n];
    print("Type ",n," numbers: ");
    for (int i=0; i<n; ++i) {
      x[i] = read();
    }
    print("Finished reading the ",n," numbers\n");
    array = x;
    size = n;
  }

  void printArray() {
    print("\n");
    for (int i=0; i<size; ++i) {
      print(array[i]," ");
    }
    print("\n");
  }

  void reverse() {
    for (int i=0; i<size/2; ++i) {
      int t = array[i];
      array[i] = array[size - i - 1];
      array[size - i - 1] = t;
    }
  }

  void insertionSort() {
    for (int i=1; i<size; ++i) {
      int v = array[i], j = i - 1;
      while (j > 0 && array[j] > v) {  // doing the loop only up to 1
        array[j + 1] = array[j];
        j = j - 1;
      }
      if (array[0] > v) {
        array[1] = array[0];
        array[0] = v;
      } else { array[j+1] = v; }
    }
  }

  void bubbleSort() {
    for (int i=0; i<size; ++i) {
      for (int j=0; j<size- 1; ++j) {
        if (array[j] > array[j + 1]) {
          int t = array[j + 1];
          array[j + 1] = array[j];
          array[j] = t;
        }
      }
    }
  }

  void siftDown(int root, int bottom) {
    bool done = false;
    int maxChild;
    while (root*2 <= bottom && !done) {
      if (root*2 == bottom) {
        maxChild = root*2;
      }
      else {
        if (array[root*2] > array[root*2 + 1]) {
          maxChild = root*2;
        }
        else {
          maxChild = root*2 + 1;
        }
      }
      if (array[root] < array[maxChild]) {
        int t = array[root];
        array[root] = array[maxChild];
        array[maxChild] = t;
        root = maxChild;
      }
      else {
        done = true;
      }
    }
  }

  void heapSort() {
    int i = size/2 - 1;
    while (i >= 0) {
      siftDown(i, size - 1);
      i = i - 1;
    }
    i = size - 1;
    while (i >= 1 ) {
      int t = array[0];
      array[0] = array[i] ;
      array[i] = t;
      siftDown(0, i - 1);
      i = i - 1;
    }
  }

}


class Main {

  void map(string[] m, (void -> void)[] f) {
    for (int i=0; i<sizeOf(f); ++i) {
      print(m[i]);
      (f[i])();
    }
  }

  void Main() {
    print("Size of the array to sort = ");
    Sorting s = new Sorting(read());
    string m[11];
    void->void f[11];
    m[ 0] = "The original unsorted array is:";
    f[ 0] = s.printArray;
    m[ 1] = "Reversing the array ... ";
    f[ 1] = s.reverse;
    m[ 2] = "Done!\nThe reversed array is:";
    f[ 2] = s.printArray;
    m[ 3] = "Sorting the array using insertion sort ... ";
    f[ 3] = s.insertionSort;
    m[ 4] = "Done!\nThe resulting array is:";
    f[ 4] = s.printArray;
    m[ 5] = "Reversing the array ... ";
    f[ 5] = s.reverse;
    m[ 6] = "Done!\nSorting the array using bubble sort ... ";
    f[ 6] = s.bubbleSort;
    m[ 7] = "Done!\nThe resulting array is:";
    f[ 7] = s.printArray;
    m[ 8] = "Reversing the array ... ";
    f[ 8] = s.reverse;
    m[ 9] = "Done!\nSorting the array using heap sort ... ";
    f[ 9] = s.heapSort;
    m[10] = "Done!\nThe resulting array is:";
    f[10] = s.printArray;
    map(m,f);
  }
}
