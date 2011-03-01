require ../../../../k-prelude

kmod OCL-SYNTAX is including K  + PL-ID + PL-INT  + PL-BOOL + PL-STRING



syntax Exp ::= Id
//Arithmetical 
               | Exp + Exp         [strict]
               | Exp * Exp         [strict]
               | Exp / Exp         [strict]
               | - Exp             [strict]
               |  Exp .size()        [strict]

//Boolean

               | Bool
               | Exp < Exp         [strict]
               | Exp <= Exp        [strict]
               | Exp > Exp         [strict]
               | Exp >= Exp        [strict]
               | Exp and Exp       [strict(1)]  
               | Exp or Exp        [strict(1)]
               | Exp implies Exp [strict(1)]
               | Exp = Exp        [strict]
               | Exp <> Exp        [strict]
               | Exp includes Exp [strict] 
               | Exp excludes Exp [strict] 
               | isEmpty ( Exp ) [strict]
               | Exp ->forAll( Id  `| Exp ) [strict (1)]
               | Exp ->exists( Id  `| Exp ) [strict (1)]
               
//  Strings               

                | String
                | Exp ++ Exp [strict] 

// Collections
                
                | empty
                | allInstances ( Id ) 
                | Id : Id
                | Exp # Id [strict(1)]  // period generates ambiguity
                | Exp union Exp [strict]
                | Exp inter Exp [strict]
                | Exp diff Exp [strict]
                | Exp ->select( Id `| Exp ) [strict (1)]
                | Exp ->collect( Id  `| Exp )  [strict (1)]
                | let Id `=   Exp  in Exp endlet [strict(2)]
                | if Exp then Exp else Exp endif [strict(1)]

// oclType

                | oclType ( Exp ) [strict]


// contents of K cell : Expressions
syntax K ::= Exp



endkm
