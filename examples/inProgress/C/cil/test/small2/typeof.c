// simple use of typeof
  
int globalInt;

void y() { 
  exit(-2);   //make sure y() is not invoked!
}

void typeofVoid() {
  (typeof(y()))0;
}


int main()
{
  __typeof(globalInt) localInt;
  typeofVoid();
  localInt  = 6 * 2 - 12;
  return localInt;
}

