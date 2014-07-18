// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module LOGIK-DESIRED2
  syntax Term ::= Literal "(" Terms ")"
  syntax Terms ::= List{Term,","}
  syntax Clause ::= Term ":-" Terms "."
  syntax Query ::= "?-" Terms "."
  syntax Pgm ::= Query | Clause Pgm

  syntax Term ::= Token{[\_A-Z][a-zA-Z0-9\_]*}                [variable, onlyLabel]
  syntax Literal ::= Token{[a-z][a-zA-Z0-9\_]*}               [onlyLabel]

  configuration <T color="yellow" multiplicity="?">
                  <k color="green"> $PGM:Pgm </k>
                  <clauses>
                    <clause color="pink" multiplicity="*"> .K </clause>
                  </clauses>
                </T>
                <solution> .K </solution>


  syntax HornClause ::=  "forall" K "." Implication         [binder]
  syntax Implication ::= Terms "->" Term

  rule <k> L:-Ls. Pgm => Pgm </k>
       (. => <clause> forall variables(L,Ls) . Ls -> L </clause>)

  rule <k> ?- Ls:Terms. => Ls ...</k>
       <solution> . => variablesMap(Ls) </solution>

  rule L:Term, Ls:Terms => L ~> Ls
  rule .Terms => .

  rule <T>... <k> . </k> ...</T> => .

  rule <k> L:Term => Ls:Terms ...</k>
       <clause> forall _ . Ls -> L </clause>
    [transition]

  syntax KItem ::= variables(K) [function, hook(MetaK:variables)]
  syntax KItem ::= variablesMap(K) [function, hook(MetaK:variablesMap)]
  syntax KItem ::= renameVariables(K) [function, hook(MetaK:renameVariables)]
endmodule
