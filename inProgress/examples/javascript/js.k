--- This file needs to be processed by the K-Maude tool


load js-syntax.k
load js-programs.k


kmod JS-SEMANTICS is including JS-SYNTAX + K
	syntax Builtin ::= String
	
	syntax KResult ::= Value | Bool | Int | Float | String 
	syntax K ::= Number | JS | List{JS} 
			
	configuration
		<T>
			<k> .K </k>
			<state> .Map </state>
	    	<I/O>
				<in> .List </in>
				<out> .List </out>
			</I/O>
		</T>

---  rule <k>X:Id => I:Int<_/k> <state_>X|->I<_/state> 
---  rule I1:Int + I2:Int => I1 +Int I2
endkm

kmod JS is including JS-PROGRAMS + JS-SEMANTICS 
  --- syntax Bag ::= [[ KLabel ]] | pgm
  --- macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  --- macro pgm = [['sumPgm]]
endkm

