load ../lib/ml-prelude.maude
load matchC-syntax
load matchC-semantics
load ../lib/fol
load ../heap_patterns/list
load ../heap_patterns/binary_tree

kmod MATCHC is
  including MATCHC-SEMANTICS
          + MATHEMATICAL-DOMAIN-BUILTIN-MODULE
          + FOL
          + LIST-HP
          + BINARY-TREE-HP

  kvar I : Int
  kvar L : List

  syntax BagItem ::= check ( K )
                   | ( Nat feasible and Nat infeasible paths)

  macro check(K:K) = <top_>
                       <check> SetItem(checkContract(id("main"))) </check>
                       <tasks>
                         <task_>
                           <program> K:K ~> checkContracts </program>
                           <k> disolveTask </k>
                         <_/task>
                       </tasks>
                     <_/top>


***(
Output
***)
  rule
    <feasible> I => I +Int 1 </feasible>
    (
      <task_>
        <program> .K </program>
        <k> disolveTask </k>
      <_/task>
    =>
      .Bag
    )
  [metadata "structural"]
  rule
    <infeasible> I => I +Int 1 </infeasible>
    (
      <task_>
        <form> FalseFormula </form>
      <_/task>
    =>
      .Bag
    )
  [metadata "structural"]
  rule
    <feasible> I => I +Int 1 </feasible>
    (
      <tasks>
        <task_>
          <program> .K </program>
          <k> .K </k>
          <out> L </out>
        <_/task>
      </tasks>
    => 
      <out> L </out>
    )
  [metadata "structural"]
endkm

