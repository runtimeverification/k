// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "builtins/model-checker.k"

module REGRESSION
  imports LTL-HOOKS
  imports MODEL-CHECKER-HOOKS

  // COMMON
  configuration <T> <thread multiplicity="*"> <k> $PGM:K </k> <holds> .Map </holds> </thread> <out stream="stdout"> .List </out> <in stream="stdin"> .List </in> <data> .List </data> <env> 5 |-> "5" .Map </env> <sum> 0 </sum> </T>
  syntax KItem ::= print(K) [strict]
  rule <k> print(I:Int) => .K ...</k> <out>... .List => ListItem(I) </out>
  syntax Common ::= Stmt | Foo

  // issue#1
  syntax Foo ::= foo1(Int, Int)
  rule foo1(I, I) => .


  // issue#2
  syntax Foo ::= foo2(Int, Int)
  rule foo2(A, B) => A +Int B


  // issue#8
  syntax KItem ::= "start1"
  rule start1 => ListItem(5) ListItem(6)
  rule <k> .List (ListItem(5) (L:List ListItem(6))) => . </k>
  rule <k> .List ((ListItem(5) L:List) ListItem(6)) => . </k>


  // tokenconstants
  syntax Id ::= "Main"
  rule K => . when K ==K Main


  // freshMOS
  syntax KItem ::= "test" |  foo19(Int)
  rule test => foo19(!X:Int)
  rule (. => !X:Id) ~> foo19(_:Int)


  // issue529
  syntax Fo ::= bar1(K)
  rule bar1(_:List) => .


  // defaultTerms1
  syntax KItem ::= "spawn"
  rule <k> spawn => . ...</k>
       (. =>
            <thread>
              ...
              <k> .K </k>
            </thread>
           )
  rule <k> spawn => . ...</k>
       (. =>
            <thread>
              <k> .K </k>
              ...
            </thread>
           )
  rule <k> spawn => . ...</k>
       (. =>
            <thread>
              ...
              <k> .K </k>
              ...
            </thread>
           )


  // openCells1
  syntax Stmt ::= "test1" | "test2"
  rule <k> test1 => . ...</k>
       <out>... .List => ListItem(1) </out>
  rule test2 => .


  // sets-issue
  syntax KItem ::= "a" | foo4(Bool)
  rule a => foo4(1 in SetItem(1))
  rule <k> foo4(true) => .K ...</k> <out>... .List => ListItem("success") </out>
  rule <k> foo4(false) => .K ...</k> <out>... .List => ListItem("fail") </out>


  //mapitem2klabel
  syntax Bool ::= "isMap4Subst" "(" Map ")" [function]
  rule isMap4Subst(I:Int |-> A:K) => true [anywhere]


  // issue
  syntax Stmt ::= "read" String
                | "flush"
        | "getInput"
  syntax Stmts ::= List{Common,";"}
  rule S:Common ; Ss:Stmts => S ~> Ss
  syntax Start ::= Stmts
  rule <k> read S:String => getInput ...</k>
       <out>... .List => ListItem(S) </out>
  rule <k> getInput => . ...</k>
       <in> ListItem(D:String) => .List ...</in>
       <data>... .List => ListItem(D) </data> [structural]
  rule <k> flush ...</k>
       <data> ListItem(D:String) => .List ...</data>
       <out>... .List => ListItem(D) </out> [structural]
  rule <k> flush => . ...</k>
       <data> .List </data> [structural]
  rule <k> S:Stmt ; Ss:Stmts => S ~> Ss ...</k> [structural]


  //issue403
  syntax SExps ::= List{SExp, " "}
  syntax SExp ::= Id | String // this is enough to reproduce the issue


  // issue466
  syntax Val ::= closure(K) [latex(a)]


  //issue483
  syntax KItem ::= foo5(Int)
  rule <k> foo5(I:Int) => M[I] </k>
       <env> M:Map </env>


  //issue#313
  syntax KLabel ::= "#foo" [function]
  syntax K ::= foo6(K)  [function, klabel(#foo)]
  rule #foo(1) => 0
  rule #foo(0) => -1


  //strictness
  syntax Foo ::= bar(Foo, Foo, Foo) [strict(1,  2), bar]
               | baz(Foo, Foo, Foo, Foo) [seqstrict(1, 3, 2)]
               | lbar(Foo, Foo)
               | lbaz(Foo, Foo)
               | foo15(Foo, Foo)
               | Int
               | "print"
  syntax KLabel ::= "'lbar" [strict, arity(2)]
                  | "'lbaz" [seqstrict, arity(2)]
  syntax KResult ::= Int
  rule <k> foo15(I:Int, I2:Int) => I +Int I2 ...</k>
       <sum> _ => I +Int I2 </sum>
  rule <k> print => . ...</k>
       <sum> I:Int </sum>
       <out>... .List => ListItem(I) </out>
  rule bar(I:Int, I2:Int, _) => .
  rule baz(I:Int, I2:Int, I3:Int, _) => .
  rule lbar(I:Int, J:Int) => .
  rule lbaz(I:Int, J:Int) => .


  //issue580
  syntax Foo ::= foo7(Int)
  rule foo7(5) => 6


  //subsort-klabel
  syntax Foo ::= Bar [klabel('foo)]
  syntax Bar ::= "bar2"
  syntax Baz ::= "baz1" Foo
  rule X:Baz => .


  //issue627
  syntax NAME ::= Id
  syntax Exp ::= NAME [atom]
               | tuple(Exp) [atom, klabel('Tuple)]
               | Exp "." NAME [primary]
  syntax priorities atom > primary
  syntax Id ::= "x"
  syntax KItem ::= foo8(K)
  rule foo8(5) => foo8(isExp(x))


  //issue631
  syntax Ints ::= List{Int,","}
  syntax Exp ::= f(Ints)
  // X must be of type Int to be completed with .Ints
  rule f(X::Int) => f(2) when X ==Int 1
  rule <k> f(2) => . </k>
       <out>... .List => ListItem(2) </out>


  //escpaedKLabel
  syntax KItem ::= "{}"
  rule <k> '`{`}(.KList) => {} ~> {} </k>


  //unparsing
  syntax Exp ::= foo(Bool, KLabel, Id, Exps)
  syntax KLabel ::= "'()"
  syntax Exp ::= "foo9"
  syntax Exps ::= List{Exp,","}


  //issue647
  syntax Stmt ::= test(Exp, Stmts, Stmts) [strict(1)]
  syntax Stmt ::= "pass"
  syntax Exp ::= Bool | Exp "==" Exp [strict]
  syntax KResult ::= Bool
  rule B:Bool == B:Bool => true
  rule test(true, _, _) => .K


  //issue663
  syntax A ::= "foo10" | "foo11"
  rule <k> foo10 => foo11 </k> <out>... .List => ListItem(5) </out> [transition]


  //issue674
  syntax Exp ::= "`" Id
  syntax Id ::= "foo12"
  syntax KItem ::= "start"
  rule <k> start => ` a ...</k> <out>... .List => ListItem("ok") </out>


  //follow
  syntax Exp ::= "&" | "&&" | Exp Exp
  syntax "&" -/- [\&]


  //issue#36
  syntax KLabel ::= "'L" [arity(1)] | "'A"
  syntax KItem ::= "dummy"
  syntax KResult ::= "res" "(" Id ")"
  context 'L(HOLE)
  rule 'A(_) => res(String2Id("X"))


  //issue#428
  syntax Exp ::= Int
               | Exp "+" Exp
               | foo13(Int)
  syntax KItem ::= foo14(Int)
  rule foo14(5) => #parse("A:Exp + foo13(A)", "Exp")


  //issue677
  syntax BBB ::= Int | foo16(BBB, BBB)
  syntax AAA ::= BBB [klabel('foo18), strict]
        | foo17(AAA, AAA) [strict]
  syntax AAA ::= Int
  rule foo16(I1:Int, I2:Int) => I1 *Int I2
  rule foo17(I1:Int, I2:Int) => I1 +Int I2
  rule 'foo18(I:Int) => I


  //label-and-context
  syntax KLabel  ::= "'ListWrap" [arity(3)] | "'B"
  context 'ListWrap(HOLE,,_:K,,_:K)
  context 'ListWrap(_:K,,HOLE,,_:K)
  context 'ListWrap(_:K,,_:K,,HOLE)
  rule 'B(_) => 1


  //cool-issue
  syntax KItem ::= "map" | "toMap"
  rule map => toMap [supercool]


  //string2int
  syntax KItem ::= "test3"
  rule test3 => #if true #then 0 #else String2Int("") #fi


  //termattributes
  syntax A ::= "foo20"


  //symbolic-sets
  syntax KItem ::= "foo21" | foo22(Set) | foo23(Set)
  rule foo21 => foo22(SetItem(1))
  rule foo22(S:Set) => foo23(S SetItem(?I:Int))
  rule foo23(S:Set) => .K


  //issue720
  syntax KItem ::= foo24(Id)
  rule <k> foo24(X:Id) => .K </k>
       <out>... .List => ListItem("Hello ") ListItem(Id2String(X)) </out>
       [hello]
  rule <k> foo24(X:Id) => .K </k>
       <out>... .List => ListItem("Bye ") ListItem(Id2String(X)) </out>
       [bye]

  // issue1219
  syntax Int ::= foo1219(Map) [function]
  rule foo1219((K1 |-> K2) M:Map) => foo1219(M)
  rule foo1219(.Map) => 0
endmodule
