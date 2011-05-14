kmod BF is
	/* \par{This is a formal semantics for the turing complete language ``brainfuck''.  Brainfuck was designed by Urban M\"uller in 1993.  More information can be found at \url{http://en.wikipedia.org/wiki/Brainfuck}.}  Some comments below are adapted from the Wikipedia article.
	
	\par{K formal semantics for BF written by Chucky Ellison (\href{mailto:celliso2@illinois.edu}{celliso2@illinois.edu}).  It is written in the ``fully labeled'' style.}
	*/
	including K
	including PL-INT
	including PL-STRING
	
// Syntax
	syntax CellLabel ::= memory
	syntax CellLabel ::= output
	syntax CellLabel ::= result
	syntax CellLabel ::= input
	syntax CellLabel ::= k

	/*@ We use an abstract syntax in this formal semantics.  The mapping from concrete to abstract syntax is given by the following chart:
	
\begin{tabular}{@{}ll@{}}
\toprule
Concrete	& Abstract\\
\midrule
\texttt{+}	& \texttt{Increase}\\
\texttt{-}	& \texttt{Decrease}\\
\texttt{>}	& \texttt{GoRight}\\
\texttt{<}	& \texttt{GoLeft}\\
\texttt{\[}	& \multirow{2}{*}{\texttt{While}}\\
\texttt{\]}	&\\
\texttt{.}	& \texttt{Print}\\
\texttt{,}	& \texttt{Read}\\
\bottomrule
\end{tabular}

Note: the \texttt{\[} and \texttt{\]} commands of BF are assumed to be matching, and are represented by a single ``While'' construct.

*/
	// comments from http://en.wikipedia.org/wiki/Brainfuck
	syntax KLabel ::= `Seq
	syntax KLabel ::= `GoRight
	syntax KLabel ::= `GoLeft
	syntax KLabel ::= `Increase
	syntax KLabel ::= `Decrease
	syntax KLabel ::= `Print
	syntax KLabel ::= `Read
	syntax KLabel ::= `While
	
// Semantics
	syntax KLabel ::= sentinel
	syntax Bag ::= eval( K )
	syntax Bag ::= eval-inp( K , K )
	syntax KResultLabel ::= int( Int )
	syntax KResultLabel ::= str( String )
	
	configuration 
		< T >
			< k > K:K </ k >
			< memory > L:List </ memory >
			< output > K:K </ output >
			< input > K:K </ input >
		</ T >  
		< result > K:K </ result > 
		
	rule [Start]: eval(K:K) => eval-inp(K:K, str("")(.List{K})) [structural]
		
	rule [Start-With-Input]: 
		eval-inp(K:K, K':K) => 
		< T >
			< k > K:K </ k >
			< memory > ListItem(sentinel(.List{K})) </ memory >
			< output > str("")(.List{K}) </ output >
			< input > K':K </ input >
		</ T >
		[structural]

	rule [Finish]: 
		< T > ?:Bag < k > .K </ k > < output > K:K </ output > </ T > 
			=> < result > K:K </ result >
		[structural]
		
	/*@ We use a sentinel to denote the edge of memory, and automatically create more memory when it is reached, */
	rule
		< memory > (.List => ListItem(int(0)(.List{K}))) ListItem(sentinel(.List{K})) ...</ memory > 
		[structural]
	
	/*@ This rule simply turns sequenced commands into the first command followed by the rest, */
	rule [Sequence]: 
		Seq(K1:K,, K2:K) => K1:K ~> K2:K
		[structural]

	/*@ \texttt{Increase}: increment (increase by one) the byte at the data pointer. */
	rule [Increase]: 
		< k > Increase(.List{K}) => .K ...</ k >
		< memory > ListItem((int(I:Int)(.List{K}) => (int(I:Int +Int 1))(.List{K}))) ...</ memory > 
	/*@ \texttt{Decrease}: decrement (decrease by one) the byte at the data pointer. */
	rule [Decrease]: 
		< k > Decrease(.List{K}) => .K ...</ k >
		< memory > ListItem((int(I:Int)(.List{K}) => (int(I:Int -Int 1))(.List{K}))) ...</ memory > 

	/*@ \texttt{GoRight}: increment the data pointer (to point to the next cell to the right).  Note that the ``data pointer'' is represented by whatever is left-most in the memory cell.  Thus, to move the pointer right, we simply roll the contents of the cell to the left.
	*/
	rule [GoRight]: 
		< k > GoRight(.List{K}) => .K ...</ k > 
		< memory > (Li:ListItem => .List) L:List (.List => Li:ListItem) </ memory > 
	/*@ \texttt{GoLeft}: decrement the data pointer (to point to the next cell to the left). */
	rule [GoLeft]: 
		< k > GoLeft(.List{K}) => .K ...</ k > 
		< memory > (.List => Li:ListItem) L:List (Li:ListItem => .List) </ memory > 
	
	/*@ \texttt{While}: if the byte at the data pointer is zero, then instead of moving the instruction pointer forward to the next command, jump it past the end of the loop.  If the byte at the data pointer is nonzero, then instead of moving the instruction pointer forward to the next command, enter the loop.
	*/
	rule [WhileNZ-NZ]: 
		< k > While(K:K) => K:K ~> While(K:K) ...</ k > 
		< memory > ListItem(int(I:Int)(.List{K})) ...</ memory > 
		if (I:Int =/=Bool 0) 
	rule [WhileNZ-Z]: 
		< k > While(K:K) => .K ...</ k >
		< memory > ListItem(int(0)(.List{K})) ...</ memory > 
	
	/*@ \texttt{Print}: output the value of the byte at the data pointer. */
	rule [Output]: 
		< k > Print(.List{K}) => .K ...</ k > 
		< memory > ListItem(I:K) ...</ memory > 
		< output > S:K => +String(S:K,, kcharString(eightbit(I:K))) </ output > 
	/*@ \texttt{Read}: accept one byte of input, storing its value in the byte at the data pointer.
	*/
	rule [Input]: 
		< k > Read(.List{K}) => .K ...</ k >
		< memory > ListItem((int(I:Int)(.List{K}) => charToAscii(firstChar(Input:K)))) ...</ memory > 
		< input > Input:K => butFirstChar(Input:K) </ input > 
		 
		
	/*@ The rest of the definition is simply helper functions. */
	syntax KLabel ::= eightbit
	rule 
		eightbit(int(I:Int)(.List{K})) 
		=> int((((I:Int %Int 256) +Int 256) %Int 256))(.List{K})
		[structural]
	
	syntax KLabel ::= kcharString
	rule 
		kcharString(int(N:Nat)(.List{K})) 
		=> str(charString(N:Nat))(.List{K})
		[structural]

	syntax KLabel ::= +String
	rule 
		+String(str(S1:String)(.List{K}),, str(S2:String)(.List{K})) 
		=> str(S1:String +String S2:String)(.List{K})
		[structural]
		
	syntax KLabel ::= firstChar
	syntax KLabel ::= butFirstChar
	syntax KLabel ::= charToAscii
	
	rule [firstChar]:
		firstChar(str(S:String)(.List{K})) => str(substrString(S:String, 0, 1))(.List{K})
		 [structural]
	rule [charToAscii]: 
		charToAscii(str(C:Char)(.List{K})) => int(asciiString(C:Char))(.List{K})
		 [structural]
	rule [butFirstChar]: 
		butFirstChar(str(S:String)(.List{K})) => str(substrString(S:String, 1, lengthString(S:String)))(.List{K})
		 [structural]
	// end helper functions
endkm

