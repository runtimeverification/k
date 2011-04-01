--- This file needs to be processed by the K-Maude tool

in ../../../k-prelude
in syntax/js-syntax
in semantics/js-semantics

kmod JS-CONFIGURATION is including JS-SYNTAX + K
	syntax KResult ::= Int | Float | Bool | String | JSPrimitive

	configuration <T> <k>.K</k> <state>.Map</state> </T>
	
	--- syntax Builtin ::= String
	--- syntax KResult ::= Value | Bool | Int | Float | String 
	--- syntax K ::= Number | JS | List{JS} 

  --- syntax K ::= AExp | BExp | Stmt
  --- syntax KResult ::= Bool | Int
  --- 
  --- configuration
  ---   <T>
  ---     <k>.K</k>
  ---     <env>.Map</env>
  ---    <store>.Map</store>
  ---    <nextLoc>0</nextLoc>
  ---    <in>.List</in>
  ---    <out>.List</out>
  ---   </T>


---  rule <k>X:Id => I:Int<_/k> <state_>X|->I<_/state> 
---  rule I1:Int + I2:Int => I1 +Int I2
endkm

kmod JS-PROGRAMS is including JS-CONFIGURATION + JS-SEMANTICS
	syntax K ::= program1

	macro program1 = #mul(#add($n(2), $n(3)), $n(4.0))
endkm

kmod JS is including  JS-PROGRAMS
	syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"] | pgm
	macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  	macro pgm = [['program1]]
endkm


