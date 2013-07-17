i = 0;
while (i < D.n) {
  p[i] = D.a[i];
  S[i] = 0;
  i = i + 1;
}
SB = empty(); 
SB.pushFront(i0);
S[i0] = 1;
// visit i0
while (SB.size() > 0) {
  i = SB.topFront();
  if (p[i].size() == 0) {
    SB.popFront();
  }
  else {
    j = p[i].topFront();
    p[i].popFront();
    if (S[j] == 0) {
      // visit j;
      S[j] = 1;
      SB.pushFront(j);
    }
  }
}

// D.n = 3
// D.a[0] = (1,2)
// D.a[1] = (2, 0)
// D.a[2] = (0)
// 
// krun programs/dfsnerec.alg -cST "D |-> { n |-> 3 a |-> { 0 |-> [1, 2, .Vals] 1 |-> [2, 0, .Vals] 2 |-> [0, .Vals] } } i0 |-> 1 p |-> { .Map } S |-> { .Map }"  -cGST=".Map"

