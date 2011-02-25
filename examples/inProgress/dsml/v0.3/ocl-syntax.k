require ../../../../k-prelude

//change names
kmod OCL-SYNTAX is including K  + PL-ID + PL-INT  + PL-BOOL 


// Expressions : Arithmetical
  syntax AExp ::= Int | Id 
               | AExp + AExp         [strict]
               | AExp * AExp         [strict]
               | AExp / AExp         [strict]
               | - AExp             [strict]
               |  CExp .size() [strict]

// Expressions : Boolean

syntax BExp ::= Bool | Id
               | AExp < AExp         [strict]
               | AExp <= AExp        [strict]
               | AExp > AExp         [strict]
               | AExp >= AExp        [strict]
               | AExp = AExp        [strict]
               | AExp <> AExp        [strict]
               | BExp and BExp       [strict]
               | BExp or BExp        [strict]
               | BExp implies BExp [strict]
               | BExp equiv BExp [strict]
               | not BExp           [strict]
               | CExp in CExp [strict] 
               | CExp in* CExp [strict] //strict inclusion
               | CExp notin CExp [strict] // negation of in
               | CExp notin* CExp [strict] // negation of in*
               | isEmpty ( CExp ) [strict]
               | CExp = CExp 
               | CExp ->forAll( Id  `| BExp ) [strict (1)]
               | CExp ->exists( Id  `| BExp ) [strict (1)]
               
               
  
// Expressions : Collections
 
syntax CExp ::= empty
                | allInstances ( Id ) 
                | Id : Id
                | AExp [strict]
                | BExp [strict]
                | CExp # Id [strict(1)]  // period generates ambiguity
                | CExp union CExp [strict]
                | CExp inter CExp [strict]
                | CExp diff CExp [strict]
                | CExp ->select( Id `| BExp ) [strict (1)]
                | CExp ->collect( Id  `| CExp )  [strict (1)]
                | let Id `=   CExp  in CExp endlet [strict(2)]
                | if BExp then CExp else CExp endif [strict(1)]


// contents of K cell : Collection expressions
syntax K ::= CExp



endkm
