module TEST-SYNTAX

  syntax TokKat ::= "ZERO"  [token]
          |"ONE" [token]

  syntax Kat ::= TokKat [hook(KAT.Kat)]
  syntax Kat ::= ".Kat" [function, functional, hook(KAT.empty), impure]

endmodule

module TEST
  imports BASIC-K
  imports TEST-SYNTAX
  imports BOOL
  imports K-EQUAL
// --------------------------------------------------------------------------------
// Boolean Algebra Part of KAT

  syntax Kat ::= Bool
                | "notKat" Kat          [function, functional, klabel(notKat_), symbol, smt-hook(not), boolOperation, latex(\neg_{\scriptstyle\it Kat}{#1}), hook(KAT.not)]
                > Kat "andKat" Kat     [function, functional, klabel(_andKat_), symbol, left, smt-hook(and), boolOperation, latex({#1}\wedge_{\scriptstyle\it Kat}{#2}), hook(KAT.and)]
                | Kat "orKat" Kat      [function, functional, klabel(_orKat_), left, smt-hook(or), boolOperation, latex({#1}\vee_{\scriptstyle\it Kat}{#2}), hook(KAT.or)]
                | Kat "=/=Kat" Kat     [function, functional, klabel(_=/=Kat_), symbol, left, smt-hook(distinct), hook(KAT.ne)]
                //| Kat "impliesKat" Kat [function, functional, klabel(_impliesKat_), symbol, left, smt-hook(=>), boolOperation, hook(KAT.implies)]

  syntax Bool ::= Kat "==Kat" Kat      [function, functional, klabel(_==Kat_), symbol, left, smt-hook(=), hook(KAT.eq)]


  syntax Kat ::= freshKat(Kat)    [freshGenerator, function]
  rule freshKat(I:Kat) => I

  rule notKat ONE => ZERO
  rule notKat ZERO => ONE

  rule ONE andKat B:Kat => B:Kat
  rule B:Kat andKat ONE => B:Kat
  rule ZERO andKat _:Kat => ZERO
  rule _:Kat andKat ZERO => ZERO

  rule ONE orKat _:Kat => ONE
  rule _:Kat orKat ONE => ONE
  rule ZERO orKat B:Kat => B
  rule B:Kat orKat ZERO => B

/*
  rule ONE impliesKat B:Kat => B
  rule ZERO impliesKat _:Kat => ONE
  rule _:Kat impliesKat ONE => ONE
  rule B:Kat impliesKat ZERO => notKat B

*/


  // ----------- MODIFICATIONS for KAT ----
  rule I1:Kat =/=Kat I2:Kat => notKat(I1 ==Kat I2)
  rule B1:Kat ==Kat B2:Kat =>  (B1 ==K B2)

  rule true:Bool => ONE
  rule false:Bool => ZERO

 // --------------------------------------------------------------------------------
  // Kleene Algebra Part of KAT


/*
    syntax Kat ::= "(" Kat ")"         [bracket]
                 > left:
                   Kat "Kat*"           [function, klabel(_starKat), symbol, left, smtlib(ka_star), latex({#1}\mathrel{\ast_{\scriptstyle\it Kat}}{#2}), hook(KAT.mul)]
                 > left:
                   Kat "Kat;" Kat       [function, klabel(_seqKat_), symbol, left, smtlib(ka_seq), latex({#1}\mathrel{+_{\scriptstyle\it Kat}}{#2}), hook(KAT.seq)]
                 > left:
                   Kat "Kat|" Kat       [function, klabel(_pllKat_), symbol, left, smtlib(ka_pll), latex({#1}\mathrel{|_{\scriptstyle\it Kat}}{#2}), hook(KAT.pll)]

*/

    syntax Kat ::= "(" Kat ")"         [bracket]
                 > left:
                   Kat "Kat*"           [function, klabel(_starKat), symbol, left, smtlib(ka_star), latex({#1}\mathrel{\ast_{\scriptstyle\it Kat}}{#2}), hook(KAT.mul)]
                | Kat "Kat;" Kat       [function, klabel(_seqKat_), symbol, left, smtlib(ka_seq), latex({#1}\mathrel{+_{\scriptstyle\it Kat}}{#2}), hook(KAT.seq)]
                | Kat "Kat|" Kat       [function, klabel(_pllKat_), symbol, left, smtlib(ka_pll), latex({#1}\mathrel{|_{\scriptstyle\it Kat}}{#2}), hook(KAT.pll)]


     rule ONE Kat; B:Kat => B:Kat
     rule B:Kat Kat; ONE => B:Kat
     rule ZERO Kat; _:Kat => ZERO
     rule _:Kat Kat; ZERO => ZERO

     // general sequential operation; why shouldn't this be used?
     // rule A:Kat Kat; B:Kat => A ~> B


     rule ONE Kat| _:Kat => ONE
     rule _:Kat Kat| ONE => ONE
     rule ZERO Kat| B:Kat => B
     rule B:Kat Kat| ZERO => B

    // Kleene-Star Operator:

     rule _B:Kat Kat* => .Kat              [klabel(_KLE_0)]
     rule B:Kat Kat* => B                 [klabel(_KLE_1)]
     rule B:Kat Kat* => B Kat; (B Kat*)   [klabel(_KLE_2)]



endmodule
