module K-SYNTAX 
  syntax Module ::= "module" Imports Sentences "end module"
  syntax Import ::= "imports" ModuleIds
  syntax ModuleIds ::= List{#Id,"+"}
  syntax Imports ::= List{Import,""}
  syntax Sentences ::= List{Sentence,""}
  syntax Sentence ::= "syntax" Syntax "[" Attrs "]"
    | "macro" Term "=" Term
    | "context" Term ("when" KTerm)? ("[" Attrs "]")?
    | "configuration" BagTerms
    | "rule" Term ("when" KTerm)? ("[" Attrs "]")?
    | "tags"  Ids
    | "declare" #Id ":" Sorts "->" Sort ("[" Attrs "]")? 
    | "define" Term ("when" KTerm)? ("[" Attrs "]")?
 
  syntax Ids ::= List{#Id,""}
  syntax Sort ::= #Id | "K" | "KLabel" | "List{K}" | "List" | "ListItem"
                | "Set" | "SetItem" | "Bag" | "BagItem" | "Map" | "MapItem"
                | "CellLabel" | "KResult"
 
  syntax Sorts ::= List{Sort,""}

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
   
   syntax Attr ::= AttrKey "(" #String ")"
   syntax AttrKey ::= #Id | "strict" | "seqstrict" | "hybrid" 
                    | "structural" | "transition" | "superheat" | "supercool"
                    | "latex" | "large"
                    | "binder"

   syntax CellAttrs ::= List{CellAttr,""}
   syntax CellAttr ::= CellAttrKey "=" #String
   
   syntax CellAttrKey ::= "multiplicity" | "color" | "open"

   syntax Variable{##X##} ::= "_" | "_:##X##" | #Id ":##X##" 
end module
