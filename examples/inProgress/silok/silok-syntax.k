/*
*  The code implements the contents of the paper:
*  "Symbolic Execution of Unbounded Object Creation"
*  by Juriaan Rot, Frank de Boer, Marcello Bonsangue
*  (LIACS - Leiden University, and CWI)
*  The focus of this file is on Section 2 in the paper.
*  SILOK - Simple Imperative Language with Object (K)Creation in K
*/


require ../../../k-prelude


kmod SILOK-SYNTAX is including PL-ID
  
  syntax ListId ::= .ListId | Id | ListId `, ListId [assoc id: .ListId] 

  syntax Pgm ::= gvars: ListId lvars: ListId flds: ListId { Procs }

  syntax Procs ::= ProcId :: B           [prec 55 gather(e E)]
                   | Procs Procs         [prec 60 gather(e E)]

  syntax ProcId ::= main | breakpoint | p0 | p1 | p2 | p3 | p4

  syntax Id ::= new  

  syntax FExp ::= Id | Id . Id [prec 40 gather(e E)]

  syntax BExp ::= Id = Id [prec 43] | Id /= Id [prec 43]

  syntax B ::= FExp := FExp              [prec 45]
               | B ; B                   [prec 50 gather(e E)] 
               | [ BExp ] B              [prec 45]
               | B + B                   [prec 48]
               | ProcId

endkm
