
int main(int y) {
  int x;
  if(y) {
    return 0;
    x ++;
  };
  // do something with x
  // It almost looks like x is a phi variable here, but it is not
  // because one of the predecessors is dead code.
  y = x + 1;
  return y;
}
