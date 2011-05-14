kmod STANDARD-MALLOC-SEMANTICS is including KERNELC-BASIC-SEMANTICS  
  rule initialLoc => 1 [structural]
  rule initial => 0 [structural] 
  rule increment(N1:Nat,N2:Nat) => N1 +Nat N2 [structural]
endkm
