#include <stdlib.h>
#include <stdio.h>
#include <time.h>
// These programs were inspired by an initiated by Josh Bloch and John Rushby, June 2006.
static int BinarySearch0(int a[], int key, int Length)
{
  int low = 0;
  int high = Length - 1;

  while (low <= high)
  {
    int mid = (low + high) / 2;
    int midVal = a[mid];

    if (midVal < key) {
      low = mid + 1;
    } else if (key < midVal) {
      high = mid - 1;
    } else {
      return mid; // key found
    }
  }
  return -(low + 1);  // key not found.
}
 
// The only difference between this version and the previous one is the initializing
// assignment of "mid" and the way the expression in the return statement is written.
// Although Boogie is not asked to confirm it here, these changes prevent arithmetic
// overflows.
static int BinarySearch2(int a[], int key, int Length)
{
  int low = 0;
  int high = Length - 1;

  while (low <= high)
  {
    int mid = low + (high - low) / 2;
    int midVal = a[mid];

    if (midVal < key) {
      low = mid + 1;
    } else if (key < midVal) {
      high = mid - 1;
    } else {
      return mid; // key found
    }
  }
  return -low - 1;  // key not found.
}

// This version adds explicit range checks.  To make the proof go through, "low <= high+1" has
// to be added as an explicit loop invariant (it is a loop invariant of the versions above, too,
// and is not inferred there either, but there it does not matter because it is not needed).

static int BinarySearch3(int a[], int key, int Length)
{
  int low = 0;
  int high = Length - 1;

  while (low <= high)
  {
    int mid = low + (high - low) / 2;
    int midVal = a[mid];

    if (midVal < key) {
      low = mid + 1;
    } else if (key < midVal) {
      high = mid - 1;
    } else {
      return mid; // key found
    }
  }

  return -low - 1;  // key not found.
}

void print(int a[], int start, int end)
{
  while(start<=end)
  {
    printf("%d ",a[start]);
    start++;
  }
  printf("\n");
}

int main()
{
  int a[30];
  int aux = 0;
  while(aux<30)
  {
    a[aux] = rand();
    aux++;
  }
  print(a,0,29);
  printf("Found: %d\n", BinarySearch3(a,5,30));
  
  return 0;
}
