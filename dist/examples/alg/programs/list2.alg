i = 3;
while (i > 0) {
  L1.pushFront(i);
  i = i-1;
}
while (L1.size() > 0) {
  L2.pushBack(L1.topFront());
  L1.popFront();
}

// krun programs/list2.alg -cST="L1 |-> [.Vals] L2 |-> [.Vals]"  -cGST=".Map"
