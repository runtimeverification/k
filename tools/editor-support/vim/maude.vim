" Vim syntax file
" Language:      K <http://fsl.cs.uiuc.edu/K>
" Maintainer:    Traian Florin Șerbănuță <tserban2@illinois.edu>
" Insipred from, and reusing most of the Maude syntax file.  
" Below is the old copyright notice:
"
" Language:      Maude <http://maude.cs.uiuc.edu/>
" Maintainer:    Steven N. Severinghaus <sns@severinghaus.org>
" Last Modified: 2005-02-03
" Version: 0.1
" To install, copy (or link) this file into the ~/.vim directory 
" and add the following to your ~/.vimrc file

" au BufRead,BufNewFile *.maude set filetype=maude
" au BufRead,BufNewFile *.kmaude set filetype=maude
" au BufRead,BufNewFile *.k set filetype=maude
" au BufRead,BufNewFile *.m set filetype=maude
" au! Syntax maude source maude.vim
" syn on


" Quit if syntax file is already loaded
if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

command! -nargs=+ MaudeHiLink hi def link <args>

syn keyword maudeModule     mod fmod omod endm endfm endm is module end
syn keyword maudeImports    protecting including extending imports
syn keyword maudeSortDecl   sort sorts subsort subsorts
syn keyword maudeStatements op ops var vars kvars kvar eq ceq rl crl rule macro context configuration mb cmb KSentence syntax tags when define declare
"syn match   maudeFlags      "\[.*\]"
syn keyword maudeCommands   reduce red rewrite rew parse frewrite frew search
syn match   maudeComment    "\*\*\*.*"
syn match   maudeComment    "---.*"
syn region  maudeComment    start="/\*"  end="\*/" contains=maudeTodo,@Spell
syn match   maudeComment    "//.*" contains=maudeTodo,@Spell
syn match   maudeOps        "->"
syn match   maudeOps        "::="
syn match   maudeOps        "|"
syn match   maudeOps        ":"
"syn match   maudeOps        "^\s*subsorts[^<]*<"hs=e-1
"syn match   maudeOps        "^\s*ceq[^=]*="
syn match   maudeOps        "="
syn match   maudeOps        "\.\s*$"

syn keyword maudeModules    CONVERSION K CONFIG 
syn match   maudeModules    "K-RULES"
syn match   maudeModules    "K-CONFIG"
syn match   maudeModules    "PL-INT"
syn match   maudeModules    "PL-ID"

syn keyword maudeSorts      K KResult KLabel KResultLabel List Bag Set Map
syn keyword maudeSorts      NeList NeMap NeBag NeSet
syn keyword maudeSorts      CellLabel ListItem BagItem SetItem MapItem

syn keyword maudeAttrs      assoc comm idem iter id left-id right-id strat memo
syn keyword maudeAttrs      prec gather format ctor config object msg frozen
syn keyword maudeAttrs      poly special label metadata owise nonexec ditto
syn keyword maudeAttrs      seqstrict strict hybrid structural transition bidirectional large superheat supercool binder  multiplicity color anywhere hook extends klabel function
syn keyword maudeAttrs      latex

syn match maudeStatements   "_" 
syn match maudeStatements   "?"
syn match maudeStatements   "\.\.\." 

syn keyword maudeLiteral    Bool Int Float Nat Qid Id
syn keyword maudeLiteral    Zero NzNat NzInt NzRat Rat FiniteFloat
syn keyword maudeLiteral    String Char FindResult DecFloat
syn keyword maudeLiteral    andBool orBool xorBool notBool impliesBool
syn keyword maudeLiteral    sNat
syn keyword maudeLiteral    true false
syn match   maudeLiteral    "\<\(0[0-7]*\|0[xX]\x\+\|\d\+\)[lL]\=\>"
syn match   maudeLiteral    "\(\<\d\+\.\d*\|\.\d\+\)\([eE][-+]\=\d\+\)\=[fFdD]\="

syn keyword maudeTodo       contained TODO FIXME XXX NOTE BUG

syn region  maudeString     start=+"+ end=+"+ contains=@Spell

MaudeHiLink maudeModule     PreProc
MaudeHiLink maudeImports    PreProc
MaudeHiLink maudeAttrs      Comment
MaudeHiLink maudeStatements Keyword
MaudeHiLink maudeModules    String
MaudeHiLink maudeComment    Comment
MaudeHiLink maudeSortDecl   Keyword
MaudeHiLink maudeOps        Special
MaudeHiLink maudeCommands   Special
MaudeHiLink maudeFlags      PreProc
MaudeHiLink maudeSorts      Type
MaudeHiLink maudeLiteral    String
MaudeHiLink maudeTodo       Todo
MaudeHiLink maudeString     String
"hi def     maudeMisc       term=bold cterm=bold gui=bold

delcommand MaudeHiLink
  
let b:current_syntax = "maude"

"EOF vim: tw=78:ft=vim:ts=8
