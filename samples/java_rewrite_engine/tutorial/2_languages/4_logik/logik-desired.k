// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module LOGIK
  syntax Term ::= Literal | Literal "(" Terms ")"
  syntax Terms ::= List{Term,","}
  syntax Clause ::= Term ":-" Terms "." | Term "." [closed] // its variables are local
  syntax Query ::= "?-" Terms "."
  syntax Pgm ::= Query | Clause Pgm

  syntax Term ::= Token{[\_A-Z][a-zA-Z0-9\_]*}                   [variable, onlyLabel]
  syntax Literal ::= Token{[a-z][a-zA-Z0-9\_]*}                  [onlyLabel]

  configuration <T color="yellow" multiplicity="?">
                  <k color="green"> $PGM:Pgm </k>
                  <clause color="pink" multiplicity="*"> .K </clause>
                </T>
                <solution multiplicity="?"> .K </solution>

  rule <k> C:Clause Pgm => Pgm </k>
       (. => <clause> C </clause>)

  rule <k> ?- Ls:Terms. => Ls ...</k>
       <solution> . => #variablesMap(Ls) </solution>  // not sure how this works

  rule L:Term, Ls:Terms => L ~> Ls
  rule .Terms => .

  rule <T>... <k> . </k> ...</T> => .

  rule <k> L:Term => Ls:Term ...</k>
       <clause> L:-Ls. </clause>
    [transition]
endmodule
