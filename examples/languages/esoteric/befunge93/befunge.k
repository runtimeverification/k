// See topmatter.tex for an overview of this language.
kmod BEFUNGE is
	including K
	including PL-BUILTINS
	
	syntax CellLabel ::= stack
	syntax CellLabel ::= direction
	syntax CellLabel ::= mode
	syntax CellLabel ::= program
	syntax CellLabel ::= pc
	syntax CellLabel ::= output
	syntax CellLabel ::= input
	syntax CellLabel ::= k
	syntax CellLabel ::= result
	syntax CellLabel ::= resultProgram
	
	syntax Bag ::= eval( K )
	syntax Bag ::= eval-inp( K , K )
	
	syntax KLabel ::= injectM( Map )
	
	syntax K ::= Int | Char | String | Bool
	
	syntax K ::= coord( K , K )
	syntax K ::= load
	syntax K ::= movePC
	syntax K ::= push( K )
	
	syntax K ::= defaultmode
	syntax K ::= stringmode
	
	configuration
		< T >
			< k > .K </ k >
			< stack > .List </ stack >
			< direction > ">" </ direction >
			< pc > coord(0, 0) </ pc >
			< mode > defaultmode </ mode >
			< program > .Map </ program >
			< output > "" </ output >
			< input > .K </ input >
		</ T >
		< result > "" </ result >
		< resultProgram > "" </ resultProgram >
	
	rule [Start]: eval(injectM(M:Map)(.List{K})) => eval-inp(injectM(M:Map)(.List{K}), "")
	rule [Start-With-Input]: eval-inp(injectM(M:Map)(.List{K}), Input:K) =>
		< T >...
			< program > M:Map </ program >
			< input > Input:K </ input >
		...</ T >
		
	/*@ \lstinline|@| (end): This command ends the program.  Because the language is reflective and can manipulate the program during runtime, we return an ascii version of the program as well.  Many Befunge programmers manipulate the program as a way of providing output.
	*/
	rule [Finish]:
		< T > S:Bag < k > "@" ...</ k > < output > S:String </ output > < program > M:Map </ program > </ T >
			=> < resultProgram > printProgram(M:Map) </ resultProgram >
			< result > S:String </ result >
		[structural]

	/*@ \lstinline|"| (stringmode): This command toggles ``stringmode'' (vs.\ ``defaultmode'').  When in stringmode, any character encountered (other than \lstinline{"}) will have its ascii value pushed onto the stack.  When in defaultmode, commands are interpreted normally.
	*/
	rule [stringmode-on]:
		< k > "\"" => .K ...</ k >
		< mode > defaultmode => stringmode </ mode >
		
	rule [stringmode-off]:
		< k > "\"" => .K ...</ k >
		< mode > stringmode => defaultmode </ mode >
	
	/*@ Any character in stringmode: If the current mode of execution is ``stringmode'', then any character other than \lstinline|"| will have its ascii value pushed onto the stack.
	*/
	rule [stringmode-push]:
		< k > C:Char => push(charToAscii(C:Char)) ...</ k >
		< mode > stringmode </ mode >
		if C:Char =/=Bool "\""
	
	// "
	
	/*@ Any number: In defaultmode, if the next ``command'' to execute is a digit, then the value of that digit should be pushed onto the stack.
	*/
	rule [defaultmode-push-number]:
		< k > C:Char => push(charToNumber(C:Char)) ...</ k >
		< mode > defaultmode </ mode >
		if isDigit(C:Char)
		
	/*@ \lstinline|>|, \lstinline|<|, \lstinline|^|, \lstinline|v|,  (right, left, up, down respectively): These commands change the direction of execution.  For example, if the program counter was moving right and encountered a \lstinline|^|, it would begin to go up.
	*/
	rule [direction]:
		< k > C:Char => .K ...</ k >
		< direction > _:Char => C:Char </ direction >
		< mode > defaultmode </ mode >
		if C:Char ==Bool ">" 
		orBool C:Char ==Bool "<"
		orBool C:Char ==Bool "^"
		orBool C:Char ==Bool "v"				
	
	/*@ \lstinline|?| (random): This command changes the direction of the program counter to be going in a random direction.
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

	/*@ \lstinline|:| (dup): This command duplicates the top element of the stack.
	*/
	rule [dup]:
		< k > ":" => .K ...</ k >
		< stack > Li:ListItem (.List => Li:ListItem) ...</ stack >
		< mode > defaultmode </ mode >
			
	/*@ \lstinline|_| (horizontal if): This command acts like \lstinline|<| if the value on the stack is true (non-zero) or \lstinline|>| if it is false.  It also pops the value off of the stack.
	*/
	rule [horizontalIf-true]:
		< k > "_" => "<" ...</ k >
		< stack > ListItem(I:Int) => .List ...</ stack >
		< mode > defaultmode </ mode >
		if I:Int =/=Bool 0
	rule [horizontalIf-false]:
		< k > "_" => ">" ...</ k >
		< stack > ListItem(I:Int) => .List ...</ stack >
		< mode > defaultmode </ mode >
		if I:Int ==Bool 0
		
	/*@ \lstinline!|! (vertical if): This command acts like \lstinline|^| if the value on the stack is true (non-zero) or \lstinline|v| if it is false.  It also pops the value off of the stack.
	*/
	rule [verticalIf-true]:
		< k > "|" => "^" ...</ k >
		< stack > ListItem(I:Int) => .List ...</ stack >
		< mode > defaultmode </ mode >
		if I:Int =/=Bool 0
	rule [verticalIf-false]:
		< k > "|" => "v" ...</ k >
		< stack > ListItem(I:Int) => .List ...</ stack >
		< mode > defaultmode </ mode >
		if I:Int ==Bool 0

	/*@ \lstinline| | (null command): This command does nothing.
	*/
	rule [nop]:
		< k > " " => .K ...</ k >	
		< mode > defaultmode </ mode >		
		
	/*@ \lstinline|$| (pop): This command pops a value off of the stack and throws it away.
	*/
	rule [pop]:
		< k > "$" => .K ...</ k >
		< stack > _:ListItem => .List ...</ stack >
		< mode > defaultmode </ mode >		
		
	/*@ \lstinline|\| (swap): This command swaps the top two elements of the stack.
	*/
	rule [swap]:
		< k > "\\" => .K ...</ k >
		< stack > Li1:ListItem Li2:ListItem => Li2:ListItem Li1:ListItem ...</ stack >
		< mode > defaultmode </ mode >

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
		if B:Int =/=Bool 0
		
	/*@ \lstinline|%| (modulo): This command pops elements $b$ and $a$ from the stack and replaces them with the modulus $a \% b$.
	*/
	rule [modulo]:
		< k > "%" => .K ...</ k >
		< stack > ListItem(B:Int) ListItem(A:Int) => ListItem(A:Int %Int B:Int) ...</ stack >
		< mode > defaultmode </ mode >
		if B:Int =/=Bool 0

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
		< program > M:Map => M:Map[safeIntToChar(V:Int) / coord(X:Int, Y:Int)] </ program >
		< mode > defaultmode </ mode >
		if (X:Int >=Int 0)
			andBool (Y:Int >=Int 0)
			andBool (X:Int <Int 80)
			andBool (Y:Int <Int 25)
	
	/*@ \lstinline|.| (output value): This command pops a number off of the stack and outputs that number as a string, followed by a space.  E.g., if the number 14 is on the stack, it will output ``14 ''.
	*/
	rule [printNumber]:
		< k > "." => .K ...</ k >
		< stack > ListItem(I:Int) => .List ...</ stack >
		< output > S:String => S:String +String Int2String(I:Int) +String " " </ output >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline|,| (output character): This command pops a number off of the stack, interprets that number as an ascii code, and outputs the corresponding character.
	*/
	rule [printCharacter]:
		< k > "," => .K ...</ k >
		< stack > ListItem(I:Int) => .List ...</ stack >
		< output > S:String => S:String +String safeIntToChar(I:Int) </ output >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline|&| (input value): This command reads a numeric value (in decimal) from the standard input, and pushes it onto the stack.  E.g., if the user types in ``32 '', it will push 32 onto the stack.
	*/
	rule [readNumber]:
		< k > "&" => readNumber(false, 0) ...</ k >
		< mode > defaultmode </ mode >
		
	/*@ \lstinline|~| (input character): This command reads a single character from the standard input, and pushes its ascii code onto the stack.
	*/
	rule [readCharacter]:
		< k > "~" => readCharacter ...</ k >
		< mode > defaultmode </ mode >		
	
	/*@ The remaining rules are used to define the helper operators and are more technical than the above rules.
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
		< direction > ">" </ direction >
		< pc > coord(I:Int => (I:Int +Int 1) %Int 80, _:K) </ pc >
		[structural]
	rule [MovePC-left]:
		< k > movePC => .K ...</ k >
		< direction > "<" </ direction >
		< pc > coord(I:Int => ((I:Int -Int 1) +Int 80) %Int 80, _:K) </ pc >
		[structural]
	rule [MovePC-up]:
		< k > movePC => .K ...</ k >
		< direction > "^" </ direction >
		< pc > coord(_:K, I:Int => ((I:Int -Int 1) +Int 25) %Int 25)  </ pc >
		[structural]
	rule [MovePC-down]:
		< k > movePC => .K ...</ k >
		< direction > "v" </ direction >
		< pc > coord(_:K, I:Int => (I:Int +Int 1) %Int 25) </ pc >
		[structural]
		
	syntax K ::= readNumber( K , K )
	syntax K ::= readCharacter
	rule [readNumber-single]:
		< k > readNumber(B:Bool => true, I:Int => I:Int +Int charToNumber(firstChar(S:String))) ...</ k >
		< input > S:String => butFirstChar(S:String) </ input >
		< mode > defaultmode </ mode >
		if isDigit(firstChar(S:String))
		[structural]
	rule [readNumber-done]:
		< k > readNumber(true, I:Int) => .K ...</ k >
		< stack > .List => ListItem(I:Int) ...</ stack >
		< input > S:String </ input >
		if notBool isDigit(firstChar(S:String))
		[structural]
	rule [readCharacter-one]:
		< k > readCharacter => .K ...</ k >
		< stack > .List => ListItem(asciiString(k2char(firstChar(S:String)))) ...</ stack >
		< input > S:String => butFirstChar(S:String) </ input >
		if asciiString(k2char(firstChar(S:String))) >=Int 0
		[structural]
		
	syntax String ::= printProgram( Map )
	syntax String ::= printProgram-aux( Int , Int , Map )
	rule printProgram(M:Map) => printProgram-aux(0, 0, M:Map) [structural]
	rule printProgram-aux(X:Int, Y:Int, M:Map)
		=> k2string(M:Map(coord(X:Int, Y:Int))) +String printProgram-aux(X:Int +Int 1, Y:Int, M:Map)
		if $hasMapping(M:Map, coord(X:Int, Y:Int))
		[structural]
	rule printProgram-aux(X:Int, Y:Int, M:Map)
		=> " " +String printProgram-aux(X:Int +Int 1, Y:Int, M:Map)
		if notBool $hasMapping(M:Map, coord(X:Int, Y:Int))
		andBool X:Int <Int 80
		andBool Y:Int <Int 25
		[structural]
	rule printProgram-aux(80, Y:Int, M:Map) => charString(10) +String printProgram-aux(0, Y:Int +Int 1, M:Map)
		[structural]
	rule printProgram-aux(0, 25, M:Map)
		=> ""
		[structural]
		
	syntax String ::= k2string( K )
	rule k2string(S:String) => S:String [structural]
	syntax Char ::= k2char( K )
	rule k2char(C:Char) => C:Char [structural]
		
	syntax Bool ::= isDigit( K )
	rule [isDigit]:
		isDigit(K:K) =>
			if (K:K ==Bool "0")
			orBool (K:K ==Bool "1")
			orBool (K:K ==Bool "2")
			orBool (K:K ==Bool "3")
			orBool (K:K ==Bool "4")
			orBool (K:K ==Bool "5")
			orBool (K:K ==Bool "6")
			orBool (K:K ==Bool "7")
			orBool (K:K ==Bool "8")
			orBool (K:K ==Bool "9")
			then true else false fi
		[structural]
		
	syntax String ::= safeIntToChar( K )
	rule safeIntToChar(I:Int) => charString(((I:Int %Int 256) +Int 256) %Int 256) [structural]
	
	syntax K ::= butFirstChar( K )
	rule [butFirstChar]:
		butFirstChar(S:String) => substrString(S:String, 1, lengthString(S:String))
		[structural]
	syntax K ::= firstChar( K )
	rule [firstChar]:
		firstChar(S:String) => substrString(S:String, 0, 1)
		[structural]
	
	syntax KLabel ::= charToAscii
	rule [charToAscii]:
		charToAscii(C:Char) => asciiString(C:Char)
		[structural]
	
	syntax Int ::= charToNumber( K )
	rule [charToNumber]:
		charToNumber(C:Char) => asciiString(C:Char) -Int asciiString("0")
		[structural]
endkm
