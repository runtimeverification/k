//test for using a typedef as void.
typedef void tVoid;

void pimInit(void);

tVoid pimInit(tVoid)
{
  return;
}

int main() {
  pimInit();
  return 0;
}
