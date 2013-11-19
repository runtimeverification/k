module LOGIK
  syntax Term ::= Literal "(" Terms ")"
  syntax Terms ::= List{Term,","}
  syntax Clause ::= Term ":-" Terms "."
                  | "forall" Set "." Terms "->" Term          [binder]
  syntax Query ::= "?-" Terms "."
  syntax Pgm ::= Query | Clause Pgm

  syntax Term ::= Token{[\_A-Z][a-zA-Z0-9\_]*}                [variable, onlyLabel]
  syntax Literal ::= Token{[a-z][a-zA-Z0-9\_]*}               [onlyLabel]

  configuration <T color="yellow" multiplicity="?">
                  <k color="green"> $PGM:Pgm </k>
                  <clause color="pink" multiplicity="*"> .K </clause>
                </T>
                <solution multiplicity="?"> .K </solution>

  rule <k> L:-Ls. Pgm => Pgm </k>
       (. => <clause> forall #variables(L,Ls) . Ls -> L </clause>)

  rule <k> ?- Ls:Terms. => Ls ...</k>
       <solution> . => #variablesMap(Ls) </solution>

  rule L:Term, Ls:Terms => L ~> Ls
  rule .Terms => .

  rule <T>... <k> . </k> ...</T> => .

  rule <k> L:Term => Ls:Term ...</k>
       <clause> forall _ . Ls -> L </clause>
    [transition]
endmodule
