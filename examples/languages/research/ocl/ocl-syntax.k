module OCL-SYNTAX is including #ID + #INT + #BOOL + #STRING

/*@ \section{Syntax}
  The current version of the \K definition of OCL includes only a kernel of the OMG standard.
  Due to the modularity of \K, the missing stuff can be incrementally added as it is needed.
*/


/*@ \subsection{Arithmetical Expressions}

*/
  syntax Exp ::= #Id | #Int
               | Exp "+" Exp         [strict prec(33) gather(E e)]
               | Exp "*" Exp         [strict prec(31) gather(E e)]
               | Exp "/" Exp         [strict prec(31) gather(E e)]
               | "-" Exp             [strict prec(29)]
               |  Exp ".size()"      [strict prec(15)]

/*@ \subsection{Boolean Expressions}

*/
  syntax Exp ::= #Bool  
               | Exp "<" Exp                          [strict prec(37) gather(E e)]
               | Exp "<=" Exp                         [strict prec(37) gather(E e)]
               | Exp ">" Exp                          [strict prec(37) gather(E e)]
               | Exp ">=" Exp                         [strict prec(37) gather(E e)]
               | Exp "and" Exp                        [strict(1) prec(39) gather(E e)]  
               | Exp "or" Exp                         [strict(1) prec(39) gather(E e)]
               | Exp "implies" Exp                    [strict(1) prec(41) gather(E e)]
               | "not" Exp                            [strict prec(29)]
               | Exp "=" Exp                          [strict prec(38) gather(E e)]
               | Exp "includes" "(" Exp ")"           [strict prec(33) gather(E e)] 
               | Exp "includesAll" "(" Exp ")"        [strict prec(33) gather(E e)] 
               | Exp "excludes" "(" Exp ")"           [strict prec(33) gather(E e)] 
               | Exp "excludesAll" "(" Exp ")"        [strict prec(33) gather(E e)] 
               | "isEmpty" "(" Exp ")"                [strict]
               | Exp "->forAll" Itr [strict(1) prec(15)]
               | Exp "->exists" Itr [strict(1) prec(15)]

  syntax Itr ::= "(" #Id  "`|" Exp ")" [binder prec(15)]
   
/*@ \subsection{String Expressions}

*/
  syntax Exp ::= #String 
                | Exp "++" Exp [strict prec(33) gather(E e)] 

/*@ \subsection{Collection Expressions}
 We consider only a single kind of collections. The right type of a collection 
 is computed by an auxiliary operator \textsf{oclType()} (this holds in fact for all expressions).
*/
  syntax Exp ::=  empty
                | #Id "." "allInstances" "(" ")"           [prec(15)]
                | Exp "." #Id                              [strict(1) prec(15)]  // period generates ambiguity
                | Exp "union" Exp                          [strict prec(33) gather(E e)]
                | Exp "->" "select" "(" #Id "`|" Exp ")"   [strict(1) prec(15)]
                | Exp "->" "collect" "(" #Id  "`|" Exp ")" [strict(1) prec(15)]
                | "let" #Id "`=" Exp "in" Exp "endlet"     [strict(2)]
                | "if" Exp "then" Exp "else" Exp "endif"   [strict(1)]
		
  syntax K ::= Exp 

end module
