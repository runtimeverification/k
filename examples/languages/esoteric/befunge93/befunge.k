kmod BEFUNGE is
	including K
	including PL-BUILTINS
	
	/*@ \par{This is a formal semantics for the language ``Befunge-93''.  Befunge-93 was designed by Chris Pressey in 1993.  It is a reflective, stack-based, two-dimensional language.  The language is not turing complete (there are a finite number of allowable input programs).  More information can be found at \url{http://en.wikipedia.org/wiki/Befunge} and \url{http://catseye.tc/projects/befunge93/}.}  Some comments below are adapted from the Wikipedia article and from the catseye webpage.
	
	\par{K formal semantics for Befunge-93 written by Chucky Ellison (\href{mailto:celliso2@illinois.edu}{celliso2@illinois.edu}).}
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

	// syntax K ::= str( String ) 
	
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
	
	
	syntax K ::= Int | Char | String
	// syntax KLabel ::= inject( Int )
	// syntax KLabel ::= inject( Char )
	// syntax KLabel ::= inject( String )
	
	syntax K ::= coord( K , K )
	syntax K ::= load
	syntax K ::= movePC
	syntax K ::= push( K )
	
	syntax K ::= defaultmode
	syntax K ::= stringmode

	syntax K ::= right
	syntax K ::= left
	syntax K ::= up
	syntax K ::= down
	
	configuration 
		< T >
			< k > .K </ k >
			< stack > .List </ stack >
			< direction > right </ direction >
			< pc > coord(0, 0) </ pc >
			< mode > defaultmode </ mode >
			< program > .Map </ program >
			< output > "" </ output >
			< input > .List </ input >
		</ T >  
		< result > K:K </ result >
	
	rule [Start]: eval(injectM(M:Map)(.List{K})) => eval-inp(injectM(M:Map)(.List{K}), injectL(.List)(.List{K}))
	rule [Start-With-Input]: eval-inp(injectM(M:Map)(.List{K}), injectL(L:List)(.List{K})) =>
		< T >...
			< program > M:Map </ program >
			< input > L:List </ input >
		...</ T >
		
	/*@ \lstinline|@| (end): This command ends the program.
	*/
	rule [Finish]: 
		< T > S:Bag < k > "@" ...</ k > < output > K:K </ output > </ T > 
			=> < result > K:K </ result >

	/*@ \lstinline|"| (stringmode): This command toggles ``stringmode'' (vs.\ ``defaultmode'').
	
	We are matching C and comparing it to the ascii value 34, instead of matching a \lstinline|"| directly due to a bug in the K tool.
	*/
	rule [stringmode-on]:
		< k > C:Char => .K ...</ k >
		< mode > defaultmode => stringmode </ mode >
		if C:Char ==Bool charString(34)
		// have to do this instead of matching "\"" because the k frontend doesn't allow quotes in strings.
		
	rule [stringmode-off]:
		< k > C:Char => .K ...</ k >
		< mode > stringmode => defaultmode </ mode >
		if C:Char ==Bool charString(34)
		
	/*@ \lstinline|>| (right): This command moves the program counter to the right by 1.
	*/
	rule [right]:
		< k > ">" => .K ...</ k >
		< direction > K:K => right </ direction >
		< mode > defaultmode </ mode >
		
		
/*@ \lstinline|<| (left): This command moves the program counter to the left by 1.
	*/
	rule [left]:
		< k > "<" => .K ...</ k >
		< direction > K:K => left </ direction >
		< mode > defaultmode </ mode >
		
		
/*@ \lstinline|^| (up): This command moves the program counter up by 1.
	*/
	rule [up]:
		< k > "^" => .K ...</ k >
		< direction > K:K => up </ direction >
		< mode > defaultmode </ mode >
		
		
/*@ \lstinline|v| (down): This command moves the program counter down by 1.
	*/
	rule [down]:
		< k > "v" => .K ...</ k >
		< direction > K:K => down </ direction >
		< mode > defaultmode </ mode >
				
	
	/*@ \lstinline|?| (random): This command moves the program counter in a random cardinal direction by 1.
	*/	
	rule [random-right]:
		< k > "?" => ">" ...</ k >
		
	rule [random-left]:
		< k > "?" => "<" ...</ k >
		
	rule [random-up]:
		< k > "?" => "^" ...</ k >
		
	rule [random-down]:
		< k > "?" => "v" ...</ k >
		
	/*@ \lstinline|#| (bridge): This command causes the next command which would normally be executed to be skipped.  That is, it causes the program counter to continue moving in the direction it was already moving, but without executing the next command.
	*/
	rule [bridge]:
		< k > "#" => movePC ...</ k >
		< mode > defaultmode </ mode >

	/*@ \lstinline|:| (dup): This command makes duplicates the top element of the stack.
	*/
	rule [dup]:
		< k > ":" => .K ...</ k >
		< stack > Li:ListItem => Li:ListItem  Li:ListItem ...</ stack >
		< mode > defaultmode </ mode >
			
	/*@ \lstinline|_| (horizontal if): This command acts like \lstinline|<| if the value on the stack is true (non-zero) or \lstinline|>| if it is false.  It pops the value off of the stack.
	*/
	rule [horizontalIf-true]:
		< k > "_" => "<" ...</ k >
		< stack > ListItem(I:Int) => .List ...</ stack >
		< mode > defaultmode </ mode >
		if (I:Int =/=Bool 0)
	rule [horizontalIf-false]:
		< k > "_" => ">" ...</ k >
		< stack > ListItem(0) => .List ...</ stack >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline!|! (vertical if): This command acts like \lstinline|^| if the value on the stack is true (non-zero) or \lstinline|v| if it is false.  It pops the value off of the stack.
	*/
	rule [verticalIf-true]:
		< k > "|" => "^" ...</ k >
		< stack > ListItem(I:Int) => .List ...</ stack >
		< mode > defaultmode </ mode >
		if (I:Int =/=Bool 0)
	rule [verticalIf-false]:
		< k > "|" => "v" ...</ k >
		< stack > ListItem(0) => .List ...</ stack >
		< mode > defaultmode </ mode >
	
	/*@ \lstinline|.| (output value): This command pops a number off of the stack and outputs that number as a string, followed by a space.  E.g., if 14 is on the stack, it will output ``14 ''.
	*/
	rule [printNumber]:
		< k > "." => .K ...</ k >
		< stack > ListItem(I:Int) => .List ...</ stack >
		< output > S:String => S:String +String Int2String((I:Int)) +String " " </ output >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline|,| (output character): This command pops a number off of the stack, interprets that number as an ascii code, and outputs the corresponding character.
	*/
	rule [printCharacter]:
		< k > "," => .K ...</ k >
		< stack > ListItem(I:Int) => .List ...</ stack >
		< output > S:String => S:String +String charString(I:Int %Int 256) </ output >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline|&| (input value): This command reads a numeric value (in decimal) from the standard input, and pushes it onto the stack.  E.g., if the user types in ``32'', it will push 32 onto the stack.
	*/
	rule [readNumber]:
		< k > "&" => .K ...</ k >
		< stack > .List => Li:ListItem ...</ stack >
		< input > Li:ListItem => .List ...</ input >
		< mode > defaultmode </ mode >
		
		
	/*@ \lstinline|~| (input character): This command reads a single character from the standard input, and pushes its ascii code onto the stack.
	*/
	rule [readCharacter]:
		< k > "~" => .K ...</ k >
		< stack > .List => ListItem(asciiString(C:Char)) ...</ stack >
		< input > ListItem(C:Char) => .List ...</ input >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline| | (null command): This command does nothing.
	*/
	rule [nop]:
		< k > " " => .K ...</ k >	
		< mode > defaultmode </ mode >		
		
	/*@ \lstinline|$| (pop): This command pops a value off of the stack and throws it away.
	*/
	rule [pop]:
		< k > "$" => .K ...</ k >
		< stack > Li:ListItem => .List ...</ stack >
		< mode > defaultmode </ mode >		
		
	/*@ \lstinline|\| (swap): This command swaps the top two elements of the stack.
	*/
	rule [swap]:
		< k > "\\" => .K ...</ k >
		< stack > Li1:ListItem Li2:ListItem => Li2:ListItem Li1:ListItem ...</ stack >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline|g| (get): This command is a meta-operation that pops the top two elements of the stack and treats them as coordinates $y$ and $x$ into the program.  The ascii value of the character that is at this position in the program is then pushed onto the stack.  If there is no code at that position, the ascii value of a null command (a space) is pushed.
	*/
	rule [metaGet]:
		< k > "g" => .K ...</ k >
		< stack > ListItem(Y:K) ListItem(X:K) => ListItem(charToAscii(K:K)) ...</ stack >
		< program >... coord(X:K, Y:K) |-> K:K ...</ program >
		< mode > defaultmode </ mode >	
		
	rule [metaGet-empty]:
		< k > "g" => .K ...</ k >
		< stack > ListItem(Y:K) ListItem(X:K) => ListItem(charToAscii(" ")) ...</ stack >
		< program > M:Map </ program >
		< mode > defaultmode </ mode >
		if notBool($hasMapping(M:Map, coord(X:K, Y:K)))
		
		
	/*@ \lstinline|p| (put): This command is a meta-operation that pops three values from the stack: a coordinate pair $y$ and $x$, and an additional value $v$.  It treats $x$ and $y$ as coordinates into the program, and writes the ascii character corresponding to value $v$ at that location in the program.
	*/
	rule [metaPut]:
		< k > "p" => .K ...</ k >
		< stack > ListItem(Y:Int) ListItem(X:Int) ListItem(V:Int) => .List ...</ stack >
		< program > M:Map => M:Map[charString(V:Int %Int 256) / coord(X:Int, Y:Int)] </ program >
		< mode > defaultmode </ mode >
		if (X:Int >=Int 0)		
			andBool (Y:Int >=Int 0)
			andBool (X:Int <Int 80)
			andBool (Y:Int <Int 25)
		
	/*@ \lstinline|!| (not): This command replaces the top element of the stack with a 1 if that element is 0, and with a 0 otherwise.
	*/
	rule [not]:
		< k > "!" => .K ...</ k >
		< stack > ListItem(I:Int) => ListItem(if (I:Int ==Bool 0) then 1 else 0 fi) ...</ stack >
		< mode > defaultmode </ mode >		
		
	/*@ \lstinline|`| (greater): This command pops the top two elements $B$ and $A$ from the stack and pushes a 1 if $A > B$, and a 0 otherwise.
	
	The rule below should show a backtick \lstinline|`| character, but due to a bug in the latex generator, it does not.
	*/
	rule [greater]:
		< k > "`" => .K ...</ k >
		< stack > ListItem(B:Int) ListItem(A:Int) => ListItem(if (A:Int >Int B:Int) then 1 else 0 fi) ...</ stack >
		< mode > defaultmode </ mode >		
		
	/*@ \lstinline|+| (add): This command pops the top two elements of the stack and replaces them with their sum.
	*/
	rule [add]:
		< k > "+" => .K ...</ k >
		< stack > ListItem(B:Int) ListItem(A:Int) => ListItem(A:Int +Int B:Int) ...</ stack >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline|-| (subtract): This command pops elements $b$ and $a$ from the stack and replaces them with the difference $a - b$.
	*/
	rule [subtract]:
		< k > "-" => .K ...</ k >
		< stack > ListItem(B:Int) ListItem(A:Int) => ListItem(A:Int -Int B:Int) ...</ stack >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline|*| (multiply): This command pops the top two elements of the stack and replaces them with their product.
	*/
	rule [multiply]:
		< k > "*" => .K ...</ k >
		< stack > ListItem(B:Int) ListItem(A:Int) => ListItem(A:Int *Int B:Int) ...</ stack >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline|/| (divide): This command pops elements $b$ and $a$ from the stack and replaces them with the integer quotient $\frac{a}{b}$.
	*/
	rule [divide]:
		< k > "/" => .K ...</ k >
		< stack > ListItem(B:Int) ListItem(A:Int) => ListItem(A:Int /Int B:Int) ...</ stack >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline|%| (modulo): This command pops elements $b$ and $a$ from the stack and replaces them with the modulus $a \% b$.
	*/
	rule [modulo]:
		< k > "%" => .K ...</ k >
		< stack > ListItem(B:Int) ListItem(A:Int) => ListItem(A:Int %Int B:Int) ...</ stack >
		< mode > defaultmode </ mode >
	
	/*@ Any number: If the next command to execute is a digit, then the value of that digit should be pushed onto the stack.
	*/
	rule [defaultmode-push-number]:
		< k > C:Char => push(charToNumber(C:Char)) ...</ k >
		< mode > defaultmode </ mode >
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
		< k > C:Char => push(charToAscii(C:Char)) ...</ k >
		< mode > stringmode </ mode >
		if (C:Char =/=Bool charString(34))
	
	
	/*@ The remaining rules are used to define the helper operators.
	*/
	rule [push]:
		< k > push(K:K) => .K ...</ k >
		< stack > .List => ListItem(K:K) ...</ stack >
		[structural]

	rule [Next]:
		< k > .K => load ~> movePC </ k >
		[structural]
		
	rule [startStack]:
		< stack > .List => ListItem(0) </ stack >
		[structural]
	rule [refillStack]:
		< stack > _:ListItem (.List => ListItem(0)) </ stack >
		[structural]
	
	rule [Load]:
		< k > load => C:Char ...</ k >
		< pc > Loc:K </ pc >
		< program >... Loc:K |-> C:Char ...</ program >
		[structural]
	rule [Load-default]:
		< k > load => " " ...</ k >
		< pc > coord(X:Int, Y:Int) </ pc >
		< program > M:Map </ program >
		if notBool($hasMapping(M:Map, coord(X:Int, Y:Int)))
			andBool (X:Int >=Int 0)
			andBool (Y:Int >=Int 0)
			andBool (X:Int <Int 80)
			andBool (Y:Int <Int 25)
		[structural]
	
	rule [MovePC-right]: 
		< k > movePC => .K ...</ k >
		< direction > right </ direction >
		< pc > coord(I:Int => (I:Int +Int 1) %Int 80, _:K) </ pc >
		[structural]
	rule [MovePC-left]: 
		< k > movePC => .K ...</ k >
		< direction > left </ direction >
		< pc > coord(I:Int => ((I:Int -Int 1) +Int 80) %Int 80, _:K) </ pc >
		[structural]
	rule [MovePC-up]: 
		< k > movePC => .K ...</ k >
		< direction > up </ direction >
		< pc > coord(_:K, I:Int => ((I:Int -Int 1) +Int 25) %Int 25)  </ pc >
		[structural]
	rule [MovePC-down]: 
		< k > movePC => .K ...</ k >
		< direction > down </ direction >
		< pc > coord(_:K, I:Int => (I:Int +Int 1) %Int 25) </ pc >
		[structural]
	
	syntax KLabel ::= charToAscii
	rule [charToAscii]:
		charToAscii(C:Char) => asciiString(C:Char)
		[structural]
	
	syntax KLabel ::= charToNumber
	rule [charToNumber]:
		charToNumber(C:Char) => asciiString(C:Char) -Int asciiString("0")
		[structural]	
endkm
