// This program tests multi-dimensional arrays.

class Matrix {
  int lines, columns;
  int[][] matrix;

  void Matrix(int x, int y) {
    lines = x;
    columns = y;
    int a[x,y];
    matrix = a;
  }

  void readMatrix() {
    for (int i=0; i<lines; ++i) {
      print("Line ", i+1, " (", columns, " elements): ");
      for (int j=0; j<columns; ++j) {
        matrix[i][j] = read();
      }
    }
  }

  void printMatrix() {
    for (int i=0; i<lines; ++i) {
      print("Line ",i+1," (",columns," elements):");
      for (int j=0; j<columns; ++j) {
        print(" ",matrix[i,j]);
      }
      print("\n");
    }
  }

  Matrix copy() {
    Matrix a = new Matrix(lines,columns);
    for (int i=0; i<lines; ++i) {
      for (int j=0; j<columns; ++j) {
        a.matrix[i,j] = matrix[i,j];
      }
    }
    return a;
  }

  void transpose() {
    int a[columns,lines];
    for (int i=0; i<lines; ++i) {
      for (int j=0; j<columns; ++j) {
        a[j,i] = matrix[i,j];
      }
    }
    int temp = lines;
    lines = columns;
    columns = temp;
    matrix = a;
  }

  void multiply(Matrix a) {
    if (a.lines != columns) {
      print("Incompatible dimensions.\n");
      return;
    }
    int b[lines,a.columns];
    for (int i=0; i<lines; ++i) {
      for (int j=0; j<a.columns; ++j) {
        b[i,j] = 0;
        for (int k=0; k<columns; ++k) {
          b[i,j] = b[i,j] + matrix[i,k] * a.matrix[k,j];
	}
      }
    }
    columns = a.columns;
    matrix = b;
  }
}


class Main {
  void Main() {
    print("Input the number of lines and columns (two natural numbers): ");
    int x = read(), y = read();
    Matrix a = new Matrix(x,y);
    a.readMatrix();
    print("Your matrix is:\n");
    a.printMatrix();
    Matrix b = a.copy();
    print("Here is a copy of your matrix:\n");
    b.printMatrix();
    print("The transpose of your matrix is:\n");
    b.transpose();
    b.printMatrix();
    print("You matrix multiplied with its transpose is:\n");
    Matrix c = a.copy();
    c.multiply(b);
    c.printMatrix();
    print("The transpose of your matrix multiplied with your matrix is:\n");
    b.multiply(a);
    b.printMatrix();
    print("Done.\n");
  }
}

// Should output what it says.
