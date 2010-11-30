--- This style is very basic, taking no advantage of K-Maude's parsing capabilities.
--- The syntax of a language is given as a set of labels, including the constants.
--- An AST is a label applied to list of labels.  The application operation is KLabel(List{K}).
--- Recall that the unit of List{K} is .List{K}, and its binary construct is ,,
--- The advantage of this style is that one encouunters no difficulties due to parsing
--- or syntax in general.  One may prefer it for real or large languages for which one
--- already has an external parser.  The disadvantage of this approach is that the ASTs
--- look rather heavy.  One may want to try the labeled-syntax style instead.

in ../../../k-prelude

kmod IMP is including PL-INT + PL-ID + K
  syntax KLabel ::= Id
  syntax KResultLabel ::=  Bool | Int

  configuration <T> <k>.K</k> <state>.Map</state> </T>
  rule <k>X:Id(.List{K}) => I:Int(.List{K})<_/k> <state_>X(.List{K})|->I(.List{K})<_/state>
  rule '+(I1:Int(.List{K}),,I2:Int(.List{K})) => (I1 +Int I2)(.List{K})
  rule '/(I1(.List{K}),,I2(.List{K})) => (I1 /Int I2)(.List{K})  if I2 =/=Bool 0
  rule '<=(I1(.List{K}),,I2(.List{K})) => (I1 <=Int I2)(.List{K})
  rule 'not(T:Bool(.List{K})) => (notBool T)(.List{K})
  rule 'and(true(.List{K}),,B:K) => B
  rule 'and(false(.List{K}),,B)  => false(.List{K})
  rule 'skip(.List{K}) => .
  rule <k>'=(X(.List{K}),,I(.List{K})) => .<_/k> <state_> X(.List{K})|->(_ => I(.List{K})) <_/state>
  rule ';(S1:K,,S2:K) => S1~>S2
  rule 'if(true(.List{K}),,S:K,,_) => S
  rule 'if(false(.List{K}),,_,,S)  => S
  rule <k>'while(B,,S) => 'if(B,,;(S,,'while(B,,S)),,'skip(.List{K})) <_/k>
  rule <k>'var('list(Kl:List{K}),,S) => S</k> <state_>. => Kl|->0(.List{K}) <_/state> [structural]

  syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"] | pgm
  macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  macro pgm = [['sumPgm]]

  macro 'sumPgm(.List{K}) =
     'var('list('n(.List{K}),,'s(.List{K})),,
         ';('=('n(.List{K}),,10(.List{K})),,
           ';('=('s(.List{K}),,0(.List{K})),,
             'while('not('<=('n(.List{K}),,0(.List{K}))),,
                   ';('=('s(.List{K}),,'+('s(.List{K}),,'n(.List{K}))),,
                     '=('n(.List{K}),,'+('n(.List{K}),,-1(.List{K}))))))))

endkm
