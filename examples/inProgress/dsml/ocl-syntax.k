require ../../../k-prelude

kmod OCL-SYNTAX is including K + PL-ID + PL-INT + PL-BOOL


  syntax Var ::= Id
  syntax Class ::= Id  // the actual classes depend on a given metamodel..
  syntax Type ::= int | bool | Class | col`(int`) | col`(bool`) | col`(Class`) // may need to add strings as well
  syntax Attr ::= Id





// Expressions : Arithmetical
  syntax AExp ::= Int | Var 
               | AExp + AExp         [strict]
               | AExp * AExp         [strict]
               | AExp / AExp         [strict]
               | - AExp             [strict]
               |  CExp .size() [strict]

// Expressions : Boolean

syntax BExp ::= Bool | Var 
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
               | CExp = CExp 
               | CExp ->forAll( Var `: Type `| BExp ) [strict (1)]
               | CExp ->exists( Var `: Type `| BExp ) [strict (1)]
               
  
// Expressions : Collections
 
syntax CExp ::= empty
                | Class .allInstances  // "basic constructor" for expressions
                | AExp [strict]
                | BExp [strict]
                | CExp # Attr [strict]  // period generates ambiguity
                | CExp union CExp [strict]
                | CExp inter CExp [strict]
                | CExp diff CExp [strict]
                | CExp ->select( Var `: Type `| BExp ) [strict (1)]
                | CExp ->collect( Var `: Type `| CExp )  [strict (1)]
                | let Var `: Type `= CExp in  CExp //[strict(3)] ?
                | if BExp then CExp else CExp endif [strict(1)]

syntax K ::= CExp


// some identifiers to test with...
// in general these will depend on a given metamodel
/*
syntax Class ::= c1 | c2 

syntax Attr ::= a1 | a2 | a3

syntax Var ::= x | y | z
*/
endkm
