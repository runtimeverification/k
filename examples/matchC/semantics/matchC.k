load ../lib/ml-prelude.maude
load matchC-syntax
load matchC-semantics
load ../lib/fol
load ../heap_patterns/list
load ../heap_patterns/binary_tree
load ../heap_patterns/io

kmod MATCHC is
  including MATCHC-SEMANTICS
          + MATHEMATICAL-DOMAIN-BUILTIN-MODULE
          + FOL
          + LIST-HP
          + BINARY-TREE-HP
          + IO-PATTERN


  kvar N : Nat
  kvar I : Int
  kvar S : String
  kvar L : List


  syntax BagItem ::= check ( K )
                   | ( Nat feasible and Nat infeasible paths)

  macro check(K:K) = <top_>
                       <check> SetItem(checkContract(id("main"))) </check>
                       <program> K:K ~> checkContracts </program>
                       <k> disolveTask </k>
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
  [structural]
  rule
    <infeasible> I => I +Int 1 </infeasible>
    (
      <task_>
        <form> FalseFormula </form>
      <_/task>
    =>
      .Bag
    )
  [structural]
  rule
    <funTask>
      <funId> .K </funId>
    </funTask>
  =>
    .Bag
  [structural]
  rule
    <funTask>
      <funId> id(S) </funId>
    </funTask>
  =>
    .Bag
  ---[structural print "maude-outputChecking " S "...Done!"]
  rule
    <feasible> I => I +Int 1 </feasible>
    (
      <tasks>
        <funTask>
          <funId> id("main") </funId>
          <task_>
            <program> .K </program>
            <k> .K </k>
            <out> L </out>
          <_/task>
        </funTask>
      </tasks>
    => 
      <out> L </out>
    )
  ---[structural print "maude-outputChecking \"main\"..Done!\nmaude-timerVerifying program...Done!"]
  [structural print "maude-output-rewritesDONE!"]
endkm

