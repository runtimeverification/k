void direct() __attribute__((noreturn));

// Pointer to function
void (*indirect)() __attribute__((noreturn)) = direct;

// An array of pointers to functions
void (* afun[2])() __attribute__((noreturn)) = { direct, direct };

void caller()
{
  direct();
  indirect();
}


int main() {
  return 0;
}
