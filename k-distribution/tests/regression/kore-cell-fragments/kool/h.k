// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"

module H-SYNTAX
imports STRING
imports INT
syntax Stmt ::= "run" "(" Int ")"
endmodule

module H

imports H-SYNTAX
imports STRING
imports INT

configuration <T>
  <k> $PGM:K </k>
  <x>
    <a> 1 </a>
    <b> 2 </b>
    <c> 3 </c>
    <d> 4 </d>
    <e multiplicity="?"> .K </e>
  </x>
</T>

syntax KItem ::= xabcde(XCellFragment) | xabcde(K)
syntax KItem ::= xabde(XCellFragment)  | xabde(K)
syntax KItem ::= xbd(XCellFragment)    | xbd(K)

rule <k> run(0) => xabde(X) ... </k>
     <x>
       X:XCellFragment
       <c> _ </c>
     </x>

rule <k> run(1) => xabcde(X <c>C</c>) ... </k>
     <x>
       X:XCellFragment
       <c> C </c>
     </x>

rule <k> run(2) => xbd(B D) ... </k>
     <x>
       <a> _ </a>
       B:BCell
       <c> C </c>
       D:DCell
     //<e> _ </e>
     </x>

rule xbd(<b> B </b> D:DCell) => B

rule <k> xabcde(<b> B </b> X) => "abcde" ... </k>
     <x>
       _ => X <b> B </b>
     </x>

rule <k> xabde(<b> B </b> X) => "abde" ... </k>
     <x>
       <c> _ </c>
       (_ => X <b> B </b>)
     </x>

syntax KItem ::= x1(XCellFragment) | x1(K)
syntax KItem ::= y1(XCellFragment) | y1(K)

rule x1(<b> B </b> X:XCellFragment) => y1(<b> 20 </b> X)

rule <k> run(3) => x1(X) ... </k>
     <x>
       X
     </x>

rule run(4) => isECell(`noECell`(.KList))
rule run(5) => isECell(`.ECell`(.KList))

endmodule
