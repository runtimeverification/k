const struct Structure {
  int field;
} structure;


typedef int Array[10];
const Array array;


void override()
{
  *((int *) array[0]) = 2;
  *((int *) &structure.field) = 1;
}
