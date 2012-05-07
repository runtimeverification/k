require "k-prelude.k"

module MODEL
	
	syntax Bag ::= "initConfig"
	
	rule [init]: initConfig => 
	<instances>
		<instances>
			<instanceName> i1 </instanceName>
			<attributes>
				
			</attributes>
		</instances>
	</instances>
	
endmodule

module OCL-SYNTAX
	imports K
		

	syntax Object ::= #Id "::" #Id
	syntax Exps ::= List{Exp,";"}  [strict]
	syntax Collection ::= "{" Exps "}"

	syntax AExp ::= #Id | #Int 
				| Collection "." "size" "(" ")" 
				> "-" AExp [strict]
				> left:
					AExp "*" AExp [left, strict]
				|	AExp "/" AExp [left, strict]
				> left:
					AExp "+" AExp [left, strict]
				|	AExp "-" AExp [left, strict]

	syntax BExp ::= #Bool 
				| "not" BExp [strict]
				> left:
					AExp "<"  AExp [left, strict]
				| AExp "<=" AExp [left, strict]
				| AExp ">"  AExp [left, strict]
				| AExp ">=" AExp [left, strict]
				> AExp "=" AExp [left, strict]
				> left:
					BExp "and" BExp [left, strict]
				| BExp "or" BExp [left, strict]
				> BExp "implies" BExp [left, strict]
				| Collection "." "isEmpty" "(" ")"

	syntax SExp ::= #String
					| SExp "+" SExp [left, strict]
	
	syntax Exp ::= AExp | BExp | SExp
				| Collection | Object
				> "(" Exp ")" [bracket]
				> Exp "union" Exp [left, strict]
				> Exp "intersection" Exp [left, strict]
				> "let" #Id "=" Exp "in" Exp "endlet" [strict(2)] 
				| "if" BExp "then" Exp "else" Exp "endif" [strict(1)]	
				
//	syntax Iter ::= #Id "|" Exp [binder]
//	syntax Iteration ::= "forAll" | "exists"

	syntax Start ::= Exp
	
endmodule

module OCL
  imports OCL-SYNTAX
  
  syntax KResult ::= #Int | #Bool | #String | Object | #Float | Collection
  
  configuration <T> 
  					<k> $PGM:K </k>
  					<trace> .List </trace>
  				</T>
  
	// arithmetic expressions
	rule [add]: I1:#Int + I2:#Int => I1 +Int I2
	rule [minus]: I1:#Int - I2:#Int => I1 -Int I2
	rule [mul]: I1:#Int * I2:#Int => I1 *Int I2
	rule [div]: I1:#Int / I2:#Int => I1 /Int I2
	rule [uminus]: - I:#Int => -Int I [structural]

	// boolean expressions  
	rule [not]: not B:#Bool => notBool(B) [structural]
	rule [and]: B1:#Bool and B2:#Bool => B1 andBool B2
	rule [or]: B1:#Bool or B2:#Bool => B1 orBool B2
	rule [implies]: B1:#Bool implies B2:#Bool => notBool(B1) andBool B2 
	
	rule [less]: I1:#Int < I2:#Int => I1 <Int I2
	rule [leq]: I1:#Int <= I2:#Int => I1 <=Int I2
	rule [greater]: I1:#Int > I2:#Int => I1 >Int I2
	rule [geq]: I1:#Int >= I2:#Int => I1 >=Int I2
	
	// string expressions
	rule [concat]: S1:#String + S2:#String => S1 +String S2
	
	
	// Collections
	
	// size
	rule [size-empty]: { .Exps } . size() => 0 [structural]
	rule [size]: { E:Exp ; Rest:Exps } . size() => 1 + { Rest } . size() [structural]
	
	// isEmpty
	rule [isEmpty-true]: { .Exps } . isEmpty() => true [structural]
	rule [isEmpty-false]: { E:Exp ; Rest:Exps } . isEmpty() => false [structural]
	
	// union
	rule [union-empty]: { C:Exps } union { .Exps } => { C } [structural]
	rule [union]: { C:Exps } union {E:Exp ; Rest:Exps} => { E ; C } union { Rest }
	
	// Other constructs
	// if
	rule [if-true] : if true  then E:Exp else _:Exp endif => E [structural]
	rule [if-false]: if false then _:Exp else E:Exp endif => E [structural]
	
endmodule 