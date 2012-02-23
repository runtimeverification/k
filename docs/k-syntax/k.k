
/*@  
  
  This file describes the syntax of K in a format similar to the current
  K syntax specification formalism.  

  This syntax cannot be currently used by the K tool to parse K; it is only    
  meant to serve as a documentation tool.

  Syntax definitional features used here but currently not supported in K:
  \begin{itemize}
    \item Optional arguments in productions, specified using ? (and brackets)
    \item Parameterized non-terminals (used for Variable)
  \end{itemize}

  Special syntactic categories
  \begin{itemize}
    \item \#Text  for arbitrary text (parsing is assumed greedy)
    \item \#Path for specifying paths
  \end{itemize}
*/

module K-SYNTAX 

  syntax File ::= List{FileItem,""}
  syntax FileItem ::= "require" #Path
                     | Module
                     | LatexComment
                     | LatexPreamble

  syntax LatexPreamble ::= "/*!" #Text "*/"
  syntax LatexComment ::= "//@" #Text "\n"
                        | "/*@" #Text "*/"
 
  syntax Module ::= "module" Imports Sentences "end module"

  syntax Import ::= "imports" ModuleIds
  syntax Imports ::= List{Import,""}

  syntax ModuleIds ::= List{#Id,"+"}
  syntax Imports ::= List{Import,""}
  syntax Sentences ::= List{Sentence,""}
  syntax Sentence ::= "syntax" Syntax
    | "macro" Term "=" Term
    | "context" Term ("when" KTerm)? ("[" Attrs "]")?
    | "configuration" BagTerms
    | "rule" Term ("when" KTerm)? ("[" Attrs "]")?
    | "tags"  Ids
    | "declare" #Id ":" Sorts "->" Sort ("[" Attrs "]")? 
    | "define" Term ("when" KTerm)? ("[" Attrs "]")?
    | LatexComment

  syntax Ids ::= List{#Id,""}
  syntax Sort ::= #Id | "K" | "KLabel" | "List{K}" | "List" | "ListItem"
                | "Set" | "SetItem" | "Bag" | "BagItem" | "Map" | "MapItem"
                | "CellLabel" | "KResult"
 
  syntax Sorts ::= List{Sort,""}

  syntax Terminal ::= #String
  syntax CFGSymbol ::= Sort | Terminal
  syntax ProdTerm ::= List{CGFSymbol,""}
  syntax Production ::= ProdTerm  ("[" Attrs "]")?

  syntax Syntax ::= List{Production,"|"}

  syntax Term ::= ListTerms | BagTerms | MapTerms | ListTerms | SetTerms
                | KLabelTerm | CellLabelTerm | KListTerms

  syntax CellLabelTerm ::= #Id | "k" | "T"
                      | CellLabelTerm "=>" CellLabelTerm
                      | Variable{CellLabel}

  syntax CellTerm ::= "<" CellLabelTerm CellAttrs? ">" Term "</" CellLabelTerm ">"

  syntax BagTerm ::= "BagItem" "(" KTerm ")" 
                   | CellTerm
                   | BagTerms "=>" BagTerms
                   | "." | ".Bag"
                   | Variable{Bag} | Variable{BagItem}
  syntax BagTerms ::= List{BagTerm,""}



  syntax SetTerm ::= "SetItem" "(" KTerm ")" 
                   | SetTerms "=>" SetTerms
                   | "." | ".Set"
                   | Variable{Set} | Variable{SetItem}
  syntax SetTerms ::= List{SetTerm,""}

  syntax MapTerm ::= KTerm "|->" KTerm 
                   | MapTerms "=>" MapTerms
                   | "." | ".Map"
                   | Variable{Map} | Variable{MapItem}
  syntax MapTerms ::= List{MapTerm,""}

  syntax ListTerm ::= "ListItem" "(" KTerm ")" 
                   | ListTerms "=>" ListTerms
                   | Variable{List} | Variable{ListItem}
                   | "." | ".List"
  syntax ListTerms ::= List{ListTerm,""}


  syntax KLabelTerm ::= #Id
                      | KLabelTerm "=>" KLabelTerm
                      | Variable{KLabel}

  syntax KItemTerm ::= KLabelTerm "(" KListTerms ")"
                | KTerm "=>" KTerm
                | "HOLE"
                | ".K"
                | Variable{K}
               // | #Int | #Bool | #Float | #String 
               // | User defined syntax 

  syntax KTerm ::= List{KItemTerm,"~>"}

  syntax KListTerm ::= KTerm
                     | ".List{K}"
                     | KListTerms "=>" KListTerms
                     | Variable{List{K}}
  syntax KListTerms ::= List{KListTerm,",,"} 


   syntax Attrs ::= List{Attr,""}
   
   syntax Attr ::= AttrKey "(" #Text ")"
   syntax AttrKey ::= #Id | "strict" | "seqstrict" | "hybrid" 
                    | "structural" | "transition" | "superheat" | "supercool"
                    | "latex" | "large"
                    | "binder"

   syntax CellAttrs ::= List{CellAttr,""}
   syntax CellAttr ::= CellAttrKey "=" #String
   
   syntax CellAttrKey ::= "multiplicity" | "color" | "open"

   syntax Variable{##X##} ::= "_" | "_:##X##" | #Id ":##X##" 
end module
