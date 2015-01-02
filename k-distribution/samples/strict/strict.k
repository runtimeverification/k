// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module STRICT

  syntax Exp ::= Val | Id
               | "(" Exp ")" [bracket]
               > "*" Exp [strict, context(rvalue), result(Ref), indirect]
               | "&" Exp [strict, indirect]
               > "++" Exp [strict]
               > Exp "+" Exp [strict, context(rvalue), result(RVal), left, plus]
               > Exp "=" Exp [strict(2), context(rvalue), result(RVal), right, assign]

  context HOLE = _


  syntax AVal ::= Int
  syntax Ref ::= "lx" | "ly" | "lz" | "lp" | "lq"  // just for examples
  syntax RVal ::= Ref | AVal
  syntax Val ::= RVal | lval(Ref)

  syntax KResult ::= Val

  syntax Id ::= "x" | "y" | "z"  // variable names
              | "p" | "q"  // pointer names

// We assume the following configuration (used in examples):

  configuration
    <k> $PGM:Exp </k>
    <env>
           x |-> lx   y |-> ly  z |-> lz
           p |-> lp   q |-> lq
    </env>
    <store> lx |-> 10 ly |-> 20 lz |-> 30 lp |-> lx lq |-> 0  </store>


  // the rule for "+"
  rule I1:Int + I2:Int => I1 +Int I2

  // the rule for "="
  rule <k> lval(L:Ref) = V:RVal => lval(L) ...</k>    // note that the result is a lvalue
       <store>... L |-> (_ => V) ...</store>

  // the rule for &

  rule & lval(L:Ref) => L

  rule * L:Ref => lval(L)

/*
  Let us also consider the following contexts for strictnness attribute that
  aloows to evaluate differently the variable names:
*/

  syntax KItem ::= "rvalue" "(" K ")" [strict, klabel(rvalue)]

/*
  A variable name always is evaluated as an lvalue
*/
  rule <k> X:Id => lval(L) ...</k>
       <env>... X |-> L:Ref ...</env>

  rule <k> ++ lval(L) => lval(L) ...</k>
       <store>... L |-> (I:Int => I +Int 1) ...</store>

  // When an l-value is in an r-value context, evaluate it
  rule <k> rvalue(lval(L:Ref) => V) ...</k>
       <store>... L |-> V:RVal ...</store>

endmodule
