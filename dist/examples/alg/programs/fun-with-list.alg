duplicate(L) {
  i = 0;
  while (i < L.size()) {
    L.update(i, 2 * L.select(i));
    i = i+1;
  }
  return L;
}

l = duplicate(l);

// krun programs/fun-with-list.alg -cST="l |-> [1, 2, 3, .Vals]" 
