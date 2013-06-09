dfsRec(i) {
  if (S[i] == 0) {
    // visit i
    S[i] = 1;
    p = D.a[i];
    while (p.size() > 0) {
      j = p.topFront();
      p.popFront();
      dfsRec(j);
    }
  }
}

// calling program
i = 0;
while (i < D.n) {
  S[i] = 0;
  i = i + 1;
}
dfsRec(1);

// D.n = 3
// D.a[0] = (1,2)
// D.a[1] = (2, 0)
// D.a[2] = (0)
// 
// krun programs/dfsrec.alg -cST ".Map" -cGST "D |-> { n |-> 3 a |-> { 0 |-> [1, 2, .Vals] 1 |-> [2, 0, .Vals] 2 |-> [0, .Vals] } } S |-> { .Map }" 

