require ../../../../k-prelude

//change names
kmod OCL-SYNTAX is including K  + PL-ID + PL-INT  + PL-BOOL + PL-STRING


// Expressions : Arithmetical
syntax Exp ::= Int | Id 
               | Exp + Exp         [strict]
               | Exp * Exp         [strict]
               | Exp / Exp         [strict]
               | - Exp             [strict]
               |  Exp .size()        [strict]

// Expressions : Boolean

               | Bool | Id
               | Exp < Exp         [strict]
               | Exp <= Exp        [strict]
               | Exp > Exp         [strict]
               | Exp >= Exp        [strict]
               | Exp = Exp        [strict]
               | Exp <> Exp        [strict]
               | Exp and Exp       [strict]
               | Exp or Exp        [strict]
               | Exp implies Exp [strict]
               | Exp equiv Exp [strict]
               | not Exp          [strict]
               | Exp in Exp [strict] 
               | Exp in* Exp [strict] //strict inclusion
               | Exp notin Exp [strict] // negation of in
               | Exp notin* Exp [strict] // negation of in*
               | isEmpty ( Exp ) [strict]
               | Exp = Exp 
               | Exp ->forAll( Id  `| Exp ) [strict (1)]
               | Exp ->exists( Id  `| Exp ) [strict (1)]
               
// Expressions : Strings               

                | String | Id
                | Exp ++ Exp [strict] 

// Expressions : Collections
 
                | empty
                | allInstances ( Id ) 
                | Id : Id
                | Exp # Id [strict(1)]  // period generates ambiguity
                | Exp `Including Exp [strict] // add 2nd arg (element) to 1st arg collection
                | Exp union Exp [strict]
                | Exp inter Exp [strict]
                | Exp diff Exp [strict]
                | Exp ->select( Id `| Exp ) [strict (1)]
                | Exp ->collect( Id  `| Exp )  [strict (1)]
                | let Id `=   Exp  in Exp endlet [strict(2)]
                | if Exp then Exp else Exp endif [strict(1)]




// contents of K cell : Expressions
syntax K ::= Exp



endkm
