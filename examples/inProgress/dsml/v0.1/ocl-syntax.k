require ../../../../k-prelude
// require k-visitor
// require substitution

kmod OCL-SYNTAX is including K  + PL-ID + PL-INT  + PL-BOOL // + SUBSTITUTION


  syntax Var ::= Id
  syntax Class ::= Id  // the actual classes depend on a given metamodel..
  syntax ScalarType ::= int | bool // may need to add strings as well
  syntax ScalarTypeCol ::= col`(int`) | col`(bool`) 
  syntax ClassTypeCol ::=  col`(Class`) 
  syntax Type ::= ScalarType | Class | ScalarTypeCol | ClassTypeCol
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
                | CExp # Attr [strict(1)]  // period generates ambiguity
                | CExp union CExp [strict]
                | CExp inter CExp [strict]
                | CExp diff CExp [strict]
                | CExp ->select( Var `: Type `| BExp ) [strict (1)]
                | CExp ->collect( Var `: Type `| CExp )  [strict (1)]
                | let Var `=   CExp  inn CExp endlet
                | if BExp then CExp else CExp endif [strict(1)]


// contents of K cell : Collection expressions
syntax K ::= CExp
// always required (?)
syntax K ::= Id



// the results of evaluating OCL expressions

syntax ValSet ::= .ValSet | Val | ValSet ValSet [hybrid gather(E e) comm id: .ValSet]
                | ValSet `Inter ValSet
                | ValSet `Diff ValSet

syntax Val ::= ScalarVal | InstVal

syntax ScalarVal ::= Bool | Int  

syntax InstVal ::=  instVal ( BagItem )


syntax KResult ::= ValSet 
syntax CExp ::= ValSet 
syntax AExp ::= Int
syntax BExp ::= Bool



endkm
