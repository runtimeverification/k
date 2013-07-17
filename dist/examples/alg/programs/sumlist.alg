s = 0;
i = 0;
while (i < L.size()) {
  s = s + L.select(i);
  i = i + 1;
}


// krun programs/sumlist.alg -cST="L |-> [1, 2, 3, .Vals]"  -cGST=".Map"
