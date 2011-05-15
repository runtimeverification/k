kmod BEFUNGE is
	including K
	including PL-BUILTINS
	
	/*@ \par{This is a formal semantics for the language ``Befunge-93''.  Befunge-93 was designed by Chris Pressey in 1993.  It is a reflective, stack-based, two-dimensional language.  The language is not turing complete (there are a finite number of allowable input programs).  More information can be found at \url{http://en.wikipedia.org/wiki/Befunge} and \url{http://catseye.tc/projects/befunge93/}.}  Some comments below are adapted from the Wikipedia article and from the catseye webpage.
	
	\par{K formal semantics for Befunge-93 written by Chucky Ellison (\href{mailto:celliso2@illinois.edu}{celliso2@illinois.edu}).  It is written in the ``fully labeled'' style.}
	*/
	
/*@
The following is a ``Hello world!'' program written in Befunge-93.
\begin{lstlisting}
                 v
>v"Hello world!"0<
,:
^_25*,@
\end{lstlisting}
*/
	
	syntax CellLabel ::= stack
	syntax CellLabel ::= direction
	syntax CellLabel ::= mode
	syntax CellLabel ::= program
	syntax CellLabel ::= pc
	syntax CellLabel ::= output
	syntax CellLabel ::= input
	syntax CellLabel ::= k
	syntax CellLabel ::= result
	
	syntax Bag ::= eval( K )
	syntax Bag ::= eval-inp( K , K )
	
	syntax KLabel ::= injectM( Map )
	syntax KLabel ::= injectL( List )
	
	syntax KLabel ::= inject( Int )
	syntax KLabel ::= inject( Char )
	syntax KLabel ::= inject( String )
	
	syntax KLabel ::= coord
	syntax KLabel ::= load
	syntax KLabel ::= defaultmode
	syntax KLabel ::= movePC
	syntax KLabel ::= stringmode
	syntax KLabel ::= push

	syntax KLabel ::= right
	syntax KLabel ::= left
	syntax KLabel ::= up
	syntax KLabel ::= down
	
	configuration 
		< T >
			< k > K:K </ k >
			< stack > L:List </ stack >
			< direction > K:K </ direction >
			< pc > K:K </ pc >
			< mode > K:K </ mode >
			< program > M:Map </ program >
			< output > K:K </ output >
			< input > L:List </ input >
		</ T >  
		< result > K:K </ result >
	
	rule [Start]: eval(injectM(M:Map)(.List{K})) => eval-inp(injectM(M:Map)(.List{K}), injectL(.List)(.List{K}))
	rule [Start-With-Input]: eval-inp(injectM(M:Map)(.List{K}), injectL(L:List)(.List{K})) =>
		< T >
			< k > .K </ k >
			< stack > .List </ stack >
			< direction > right(.List{K}) </ direction >
			< pc > coord(inject(0)(.List{K}),, inject(0)(.List{K})) </ pc >
			< mode > defaultmode(.List{K}) </ mode >
			< program > M:Map </ program >
			< output > inject("")(.List{K}) </ output >
			< input > L:List </ input >
		</ T >
		
	/*@ \lstinline|@| (end): This command ends the program.
	*/
	rule [Finish]: 
		< T > S:Bag < k > inject("@")(.List{K}) ...</ k > < output > K:K </ output > </ T > 
			=> < result > K:K </ result >

	/*@ \lstinline|"| (stringmode): This command toggles ``stringmode'' (vs.\ ``defaultmode'').
	
	We are matching C and comparing it to the ascii value 34, instead of matching a \lstinline|"| directly due to a bug in the K tool.
	*/
	rule [stringmode-on]:
		< k > inject(C:Char)(.List{K}) => .K ...</ k >
		< mode > defaultmode(.List{K}) => stringmode(.List{K}) </ mode >
		if C:Char ==Bool charString(34)
		// have to do this instead of matching "\"" because the k frontend doesn't allow quotes in strings.
		
	rule [stringmode-off]:
		< k > inject(C:Char)(.List{K}) => .K ...</ k >
		< mode > stringmode(.List{K}) => defaultmode(.List{K}) </ mode >
		if C:Char ==Bool charString(34)
		
	/*@ \lstinline|>| (right): This command moves the program counter to the right by 1.
	*/
	rule [right]:
		< k > inject(">")(.List{K}) => .K ...</ k >
		< direction > K:K => right(.List{K}) </ direction >
		< mode > defaultmode(.List{K}) </ mode >
		
		
/*@ \lstinline|<| (left): This command moves the program counter to the left by 1.
	*/
	rule [left]:
		< k > inject("<")(.List{K}) => .K ...</ k >
		< direction > K:K => left(.List{K}) </ direction >
		< mode > defaultmode(.List{K}) </ mode >
		
		
/*@ \lstinline|^| (up): This command moves the program counter up by 1.
	*/
	rule [up]:
		< k > inject("^")(.List{K}) => .K ...</ k >
		< direction > K:K => up(.List{K}) </ direction >
		< mode > defaultmode(.List{K}) </ mode >
		
		
/*@ \lstinline|v| (down): This command moves the program counter down by 1.
	*/
	rule [down]:
		< k > inject("v")(.List{K}) => .K ...</ k >
		< direction > K:K => down(.List{K}) </ direction >
		< mode > defaultmode(.List{K}) </ mode >
				
	
	/*@ \lstinline|?| (random): This command moves the program counter in a random cardinal direction by 1.
	*/	
	rule [random-right]:
		< k > inject("?")(.List{K}) => inject(">")(.List{K}) ...</ k >
		
	rule [random-left]:
		< k > inject("?")(.List{K}) => inject("<")(.List{K}) ...</ k >
		
	rule [random-up]:
		< k > inject("?")(.List{K}) => inject("^")(.List{K}) ...</ k >
		
	rule [random-down]:
		< k > inject("?")(.List{K}) => inject("v")(.List{K}) ...</ k >
		
	/*@ \lstinline|#| (bridge): This command causes the next command which would normally be executed to be skipped.  That is, it causes the program counter to continue moving in the direction it was already moving, but without executing the next command.
	*/
	rule [bridge]:
		< k > inject("#")(.List{K}) => movePC(.List{K}) ...</ k >
		< mode > defaultmode(.List{K}) </ mode >

	/*@ \lstinline|:| (dup): This command makes duplicates the top element of the stack.
	*/
	rule [dup]:
		< k > inject(":")(.List{K}) => .K ...</ k >
		< stack > Li:ListItem => Li:ListItem  Li:ListItem ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
			
	/*@ \lstinline|_| (horizontal if): This command acts like \lstinline|<| if the value on the stack is true (non-zero) or \lstinline|>| if it is false.  It pops the value off of the stack.
	*/
	rule [horizontalIf-true]:
		< k > inject("_")(.List{K}) => inject("<")(.List{K}) ...</ k >
		< stack > ListItem(inject(I:Int)(.List{K})) => .List ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
		if (I:Int =/=Bool 0)
	rule [horizontalIf-false]:
		< k > inject("_")(.List{K}) => inject(">")(.List{K}) ...</ k >
		< stack > ListItem(inject(0)(.List{K})) => .List ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
		
	/*@ \lstinline!|! (vertical if): This command acts like \lstinline|^| if the value on the stack is true (non-zero) or \lstinline|v| if it is false.  It pops the value off of the stack.
	*/
	rule [verticalIf-true]:
		< k > inject("|")(.List{K}) => inject("^")(.List{K}) ...</ k >
		< stack > ListItem(inject(I:Int)(.List{K})) => .List ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
		if (I:Int =/=Bool 0)
	rule [verticalIf-false]:
		< k > inject("|")(.List{K}) => inject("v")(.List{K}) ...</ k >
		< stack > ListItem(inject(0)(.List{K})) => .List ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
	
	/*@ \lstinline|.| (output value): This command pops a number off of the stack and outputs that number as a string, followed by a space.  E.g., if 14 is on the stack, it will output ``14 ''.
	*/
	rule [printNumber]:
		< k > inject(".")(.List{K}) => .K ...</ k >
		< stack > ListItem(inject(I:Int)(.List{K})) => .List ...</ stack >
		< output > inject(S:String)(.List{K}) => inject(S:String +String Int2String(absInt(I:Int)) +String " ")(.List{K}) </ output >
		< mode > defaultmode(.List{K}) </ mode >
		
	/*@ \lstinline|,| (output character): This command pops a number off of the stack, interprets that number as an ascii code, and outputs the corresponding character.
	*/
	rule [printCharacter]:
		< k > inject(",")(.List{K}) => .K ...</ k >
		< stack > ListItem(inject(I:Int)(.List{K})) => .List ...</ stack >
		< output > inject(S:String)(.List{K}) => inject(S:String +String charString(absInt(I:Int %Int 256)))(.List{K}) </ output >
		< mode > defaultmode(.List{K}) </ mode >
		
	/*@ \lstinline|&| (input value): This command reads a numeric value (in decimal) from the standard input, and pushes it onto the stack.  E.g., if the user types in ``32'', it will push 32 onto the stack.
	*/
	rule [readNumber]:
		< k > inject("&")(.List{K}) => .K ...</ k >
		< stack > .List => Li:ListItem ...</ stack >
		< input > Li:ListItem => .List ...</ input >
		< mode > defaultmode(.List{K}) </ mode >
		
		
	/*@ \lstinline|~| (input character): This command reads a single character from the standard input, and pushes its ascii code onto the stack.
	*/
	rule [readCharacter]:
		< k > inject("~")(.List{K}) => .K ...</ k >
		< stack > .List => ListItem(inject(asciiString(C:Char))(.List{K})) ...</ stack >
		< input > ListItem(inject(C:Char)(.List{K})) => .List ...</ input >
		< mode > defaultmode(.List{K}) </ mode >
		
	/*@ \lstinline| | (null command): This command does nothing.
	*/
	rule [nop]:
		< k > inject(" ")(.List{K}) => .K ...</ k >	
		< mode > defaultmode(.List{K}) </ mode >		
		
	/*@ \lstinline|$| (pop): This command pops a value off of the stack and throws it away.
	*/
	rule [pop]:
		< k > inject("$")(.List{K}) => .K ...</ k >
		< stack > Li:ListItem => .List ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >		
		
	/*@ \lstinline|\| (swap): This command swaps the top two elements of the stack.
	*/
	rule [swap]:
		< k > inject("\\")(.List{K}) => .K ...</ k >
		< stack > Li1:ListItem Li2:ListItem => Li2:ListItem Li1:ListItem ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
		
	/*@ \lstinline|g| (get): This command is a meta-operation that pops the top two elements of the stack and treats them as coordinates $y$ and $x$ into the program.  The ascii value of the character that is at this position in the program is then pushed onto the stack.  If there is no code at that position, the ascii value of a null command (a space) is pushed.
	*/
	rule [metaGet]:
		< k > inject("g")(.List{K}) => .K ...</ k >
		< stack > ListItem(Y:K) ListItem(X:K) => ListItem(charToAscii(K:K)) ...</ stack >
		< program >... coord(X:K,, Y:K) |-> K:K ...</ program >
		< mode > defaultmode(.List{K}) </ mode >	
		
	rule [metaGet-empty]:
		< k > inject("g")(.List{K}) => .K ...</ k >
		< stack > ListItem(Y:K) ListItem(X:K) => ListItem(charToAscii(inject(" ")(.List{K}))) ...</ stack >
		< program > M:Map </ program >
		< mode > defaultmode(.List{K}) </ mode >
		if notBool($hasMapping(M:Map, coord(X:K,, Y:K)))
		
		
	/*@ \lstinline|p| (put): This command is a meta-operation that pops three values from the stack: a coordinate pair $y$ and $x$, and an additional value $v$.  It treats $x$ and $y$ as coordinates into the program, and writes the ascii character corresponding to value $v$ at that location in the program.
	*/
	rule [metaPut]:
		< k > inject("p")(.List{K}) => .K ...</ k >
		< stack > ListItem(inject(Y:Int)(.List{K})) ListItem(inject(X:Int)(.List{K})) ListItem(inject(V:Int)(.List{K})) => .List ...</ stack >
		< program > M:Map => M:Map[inject(charString(absInt(V:Int %Int 256)))(.List{K}) / coord(inject(X:Int)(.List{K}),, inject(Y:Int)(.List{K}))] </ program >
		< mode > defaultmode(.List{K}) </ mode >
		if (X:Int >=Int 0)		
			andBool (Y:Int >=Int 0)
			andBool (X:Int <Int 80)
			andBool (Y:Int <Int 25)
		
	/*@ \lstinline|!| (not): This command replaces the top element of the stack with a 1 if that element is 0, and with a 0 otherwise.
	*/
	rule [not]:
		< k > inject("!")(.List{K}) => .K ...</ k >
		< stack > ListItem(inject(I:Int)(.List{K})) => ListItem(inject(if (I:Int ==Bool 0) then 1 else 0 fi)(.List{K})) ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >		
		
	/*@ \lstinline|`| (greater): This command pops the top two elements $b$ and $a$ from the stack and pushes a 1 if $a > b$, and a 0 otherwise.
	*/
	rule [greater]:
		< k > inject("`")(.List{K}) => .K ...</ k >
		< stack > ListItem(inject(I2:Int)(.List{K})) ListItem(inject(I1:Int)(.List{K})) => ListItem(inject(if (I1:Int >Int I2:Int) then 1 else 0 fi)(.List{K})) ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >		
		
	/*@ \lstinline|+| (add): This command pops the top two elements of the stack and replaces them with their sum.
	*/
	rule [add]:
		< k > inject("+")(.List{K}) => .K ...</ k >
		< stack > ListItem(inject(I1:Int)(.List{K})) ListItem(inject(I2:Int)(.List{K})) => ListItem(inject(I2:Int +Int I1:Int)(.List{K})) ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
		
	/*@ \lstinline|-| (subtract): This command pops elements $b$ and $a$ from the stack and replaces them with the difference $a - b$.
	*/
	rule [subtract]:
		< k > inject("-")(.List{K}) => .K ...</ k >
		< stack > ListItem(inject(I1:Int)(.List{K})) ListItem(inject(I2:Int)(.List{K})) => ListItem(inject(I2:Int -Int I1:Int)(.List{K})) ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
		
	/*@ \lstinline|*| (multiply): This command pops the top two elements of the stack and replaces them with their product.
	*/
	rule [multiply]:
		< k > inject("*")(.List{K}) => .K ...</ k >
		< stack > ListItem(inject(I1:Int)(.List{K})) ListItem(inject(I2:Int)(.List{K})) => ListItem(inject(I2:Int *Int I1:Int)(.List{K})) ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
		
	/*@ \lstinline|/| (divide): This command pops elements $b$ and $a$ from the stack and replaces them with the integer quotient $\frac{a}{b}$.
	*/
	rule [divide]:
		< k > inject("/")(.List{K}) => .K ...</ k >
		< stack > ListItem(inject(I1:Int)(.List{K})) ListItem(inject(I2:Int)(.List{K})) => ListItem(inject(I2:Int /Int I1:Int)(.List{K})) ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
		
	/*@ \lstinline|/| (divide): This command pops elements $b$ and $a$ from the stack and replaces them with the modulus $a \% b$.
	*/
	rule [modulo]:
		< k > inject("%")(.List{K}) => .K ...</ k >
		< stack > ListItem(inject(I1:Int)(.List{K})) ListItem(inject(I2:Int)(.List{K})) => ListItem(inject(I2:Int %Int I1:Int)(.List{K})) ...</ stack >
		< mode > defaultmode(.List{K}) </ mode >
	
	/*@ Any number: If the next command to execute is a digit, then the value of that digit should be pushed onto the stack.
	*/
	rule [defaultmode-push-number]:
		< k > inject(C:Char)(.List{K}) => push(charToNumber(inject(C:Char)(.List{K}))) ...</ k >
		< mode > defaultmode(.List{K}) </ mode >
		if (C:Char ==Bool "0") 
			orBool (C:Char ==Bool "1") 
			orBool (C:Char ==Bool "2")
			orBool (C:Char ==Bool "3") 
			orBool (C:Char ==Bool "4")
			orBool (C:Char ==Bool "5")
			orBool (C:Char ==Bool "6")
			orBool (C:Char ==Bool "7")
			orBool (C:Char ==Bool "8")
			orBool (C:Char ==Bool "9")
	
	/*@ Any character in stringmode: If the current mode of execution is ``stringmode'', then any character other than \lstinline|"| will have its ascii value pushed onto the stack.
	*/
	rule [stringmode-push]:
		< k > inject(C:Char)(.List{K}) => push(charToAscii(inject(C:Char)(.List{K}))) ...</ k >
		< mode > stringmode(.List{K}) </ mode >
		if (C:Char =/=Bool charString(34))
	
	
	/*@ The remaining rules are used to define the helper operators.
	*/
	rule [push]:
		< k > push(K:K) => .K ...</ k >
		< stack > .List => ListItem(K:K) ...</ stack >
		[structural]

	rule [Next]:
		< k > .K => load(.List{K}) ~> movePC(.List{K}) </ k >
		[structural]
		
	rule [startStack]:
		< stack > .List => ListItem(inject(0)(.List{K})) </ stack >
		[structural]
	rule [refillStack]:
		< stack > Li:ListItem => Li:ListItem ListItem(inject(0)(.List{K})) </ stack >
		[structural]
	
	rule [Load]:
		< k > load(.List{K}) => inject(C:Char)(.List{K}) ...</ k >
		< pc > Loc:K </ pc >
		< program >... Loc:K |-> inject(C:Char)(.List{K}) ...</ program >
		[structural]
	rule [Load-default]:
		< k > load(.List{K}) => inject(" ")(.List{K}) ...</ k >
		< pc > coord(inject(X:Int)(.List{K}),, inject(Y:Int)(.List{K})) </ pc >
		< program > M:Map </ program >
		if notBool($hasMapping(M:Map, coord(inject(X:Int)(.List{K}),, inject(Y:Int)(.List{K}))))
			andBool (X:Int >=Int 0)
			andBool (Y:Int >=Int 0)
			andBool (X:Int <Int 80)
			andBool (Y:Int <Int 25)
		[structural]
	
	rule [MovePC-right]: 
		< k > movePC(.List{K}) => .K ...</ k >
		< direction > right(.List{K}) </ direction >
		< pc > coord(inject(I:Int)(.List{K}),, K:K) => coord(inject((I:Int +Int 1) %Int 80)(.List{K}),, K:K) </ pc >
		[structural]
	rule [MovePC-left]: 
		< k > movePC(.List{K}) => .K ...</ k >
		< direction > left(.List{K}) </ direction >
		< pc > coord(inject(I:Int)(.List{K}),, K:K) => coord(inject(((I:Int -Int 1) +Int 80) %Int 80)(.List{K}),, K:K) </ pc >
		[structural]
	rule [MovePC-up]: 
		< k > movePC(.List{K}) => .K ...</ k >
		< direction > up(.List{K}) </ direction >
		< pc > coord(K:K,, inject(I:Int)(.List{K})) => coord(K:K,, inject(((I:Int -Int 1) +Int 25) %Int 25)(.List{K})) </ pc >
		[structural]
	rule [MovePC-down]: 
		< k > movePC(.List{K}) => .K ...</ k >
		< direction > down(.List{K}) </ direction >
		< pc > coord(K:K,, inject(I:Int)(.List{K})) => coord(K:K,, inject((I:Int +Int 1) %Int 25)(.List{K})) </ pc >
		[structural]
	
	syntax KLabel ::= charToAscii
	rule [charToAscii]:
		charToAscii(inject(C:Char)(.List{K})) => inject(asciiString(C:Char))(.List{K})
		[structural]
	
	syntax KLabel ::= charToNumber
	rule [charToNumber]:
		charToNumber(inject(C:Char)(.List{K})) => inject(asciiString(C:Char) -Int asciiString("0"))(.List{K})
		[structural]
	// end structural
	
endkm
