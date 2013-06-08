ArrList::update(i, x) {
  self.arr[i] = x;
}

ArrList::pushFront(x) {
  i = self.length;
  while (i > 0) {
    self.arr[i] = self.arr[i-1];
    i = i-1;
  }
  self.arr[0] = x;
}

l.ArrList::pushFront(1);
l.pushFront(2);
l.update(0,5);

// krun programs/list-with-arrays.alg -cST "l |-> { length |-> 2 arr |-> { 0 |-> 7 1 |-> 8 2 |-> 9 3 |-> 0} }"

