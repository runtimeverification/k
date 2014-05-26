// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module META
  syntax KItem ::= renameVariables(K)   [function, hook(MetaK:renameVariables)]
  syntax KItem ::= variables(K)         [function, hook(MetaK:variables)]
  syntax KItem ::= variablesMap(K)      [function, hook(MetaK:variablesMap)]

  syntax Bool ::= unifiable(K,K) [function, hook(MetaK:unifiable)]
endmodule

module LOGIK2
  imports META
  syntax Term ::= Literal | Literal "(" Terms ")"
  syntax Terms ::= List{Term,","}
  syntax Clause ::= Term ":-" Terms "." | Term "."
  syntax Query ::= "?-" Terms "."
  syntax Pgm ::= Query | Clause Pgm

  syntax Term ::= Token{[\_A-Z][a-zA-Z0-9\_]*}                   [variable, onlyLabel]
  syntax Literal ::= Token{[a-z][a-zA-Z0-9\_]*}                  [onlyLabel]

  configuration <T color="yellow" multiplicity="?">
                  <k color="green"> $PGM:Pgm </k>
                  <clauses color="red">
                    <clause color="pink" multiplicity="*"> .K </clause>
                  </clauses>
                  <mgu> .K </mgu>
                </T>
                <solution multiplicity="?"> .K </solution>

  rule <k> C:Clause Pgm => Pgm </k>
       (. => <clause> renameVariables(C) </clause>)

  rule <k> ?- Ls:Terms. => Ls ...</k>
       <mgu> _ => variablesMap(variables(Ls)) </mgu>

  rule L:Term, Ls:Terms => L ~> Ls
  rule .Terms => .

  rule <T>... <k> . </k> <mgu> Theta </mgu> ...</T>
    => <solution> Theta </solution>

  rule <k> L:Term => Ls:Term ...</k>
       <clause> L:-Ls. => renameVariables(L:-Ls.) </clause>
    [transition]
endmodule
