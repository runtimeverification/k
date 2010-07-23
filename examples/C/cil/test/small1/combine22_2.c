// Fill in the old empty struct


typedef int MYINT;

struct empty {
  MYINT i;
} glob;

struct empty  *ptr_empty;

int main() {
  return glob.i;
}
