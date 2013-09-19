" Vim syntax file
" Language:      K <k-framework.org>
" Maintainers:   Andrei Ștefănescu <stefane1@illinois.edu>
"                Traian Florin Șerbănuță <tserban2@illinois.edu>
" Inspired from, and reusing most of the Maude file.
" Below is the old copyright notice:
"
" Language:      Maude <http://maude.cs.uiuc.edu/>
" Maintainer:    Steven N. Severinghaus <sns@severinghaus.org>
" Last Modified: 2005-02-03
" Version: 0.1
"
" To install, copy (or link) this file into the ~/.vim/syntax directory and add
" the following to the ~/.vimrc file
"
" au BufRead,BufNewFile *.k set filetype=kframework
" syn on


" Quit if syntax file is already loaded
if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

command! -nargs=+ KHiLink hi def link <args>

syn keyword kRequire      require nextgroup=kRequireFile skipwhite
syn region  kRequireFile  contained start=+"+ end=+"+
 
syn keyword kModule       module nextgroup=kModuleName skipwhite endmodule
syn keyword kImports      imports nextgroup=kModuleName skipwhite
" not sure why \h is required, but it does not match without it
syn match   kModuleName   contained "#\=\h\(\w\|-\)*"

syn keyword kSyntax       syntax nextgroup=kSyntaxName skipwhite
syn match   kSyntaxName   contained "#\=\u\w*\({\s*#\=\u\w*\(\s*,\s*#\=\u\w*\)*\s*}\)*"
syn keyword kSyntaxAttr   left right prefer avoid
syn match   kSyntaxAttr   "\<non-assoc\>"

syn keyword kStatement    configuration rule context when where requires ensures

" the following is just for folding (Ctrl-F9), currently not working
syn region  kCellContent  start="<\h\(\w\|-\)*>" end="</\h\(\w\|-\)*>" fold transparent

syn match   kCell         /<\h\(\w\|-\)*\(\s\+\l\+="[^"]*"\)*>/ contains=kCellAttr,kString
syn match   kCell         "<\/\h\(\w\|-\)*>"
syn match   kCell         "\.\.\."

syn match   kCellAttr "\l\+=" contained contains=kEqual
syn match   kEqual        "=" contained

syn match   kSymbol       "::="
syn match   kSymbol       "=>"
syn keyword kSymbol       HOLE

syn match   kMeta         "\s\[[^[\]]*\]\s*$"

syn keyword kType         K KItem KResult KLabel KList
syn keyword kType         List Bag Set Map
syn keyword kType         NeList NeMap NeBag NeSet
syn keyword kType         ListItem BagItem SetItem MapItem
syn keyword kType         CellLabel
syn keyword kType         Bool Int Nat Float String Char Id
syn keyword kType         #Bool #Int #Float #String #Char #Id

" syn keyword kAttrs        bidirectional superheat supercool
" syn keyword kAttrs        function predicate seqstrict strict hybrid binder
" syn keyword kAttrs        klabel prefixlabel hook latex smt
" syn keyword kAttrs        structural transition anywhere macro
" syn keyword kAttrs        multiplicity color
" 
" syn keyword kLiteral      andBool orBool xorBool notBool impliesBool

syn keyword kBoolean    true false
syn match   kNumber     "\<\(0\o\+\|0[xX]\x\+\|\d\+\)[lL]\=\>"
syn match   kFloat      "\(\<\d\+\.\d*\|\.\d\+\)\([eE][-+]\=\d\+\)\=[fFdD]\="
syn region  kString     start=+"+ skip=+\\\\\|\\"+ end=+"+ end=+$+ contains=@Spell

syn region  kComment    start="/\*" end="\*/" contains=kTodo,@Spell
syn match   kComment    "//.*$" contains=kTodo,@Spell
syn keyword kTodo       contained TODO FIXME XXX NOTE BUG


KHiLink kRequire        Include
KHiLink kRequireFile    Include
KHiLink kModule         Keyword
KHiLink kImports        Keyword
KHiLink kModuleName     Type
KHiLink kSyntax         Statement
KHiLink kSyntaxName     Type
KHiLink kSyntaxAttr     StorageClass
KHiLink kStatement      Statement
" KHiLink kCellContent    PreProc
KHiLink kCell           Structure
KHiLink kCellAttr       Structure
KHiLink kMeta           PreProc
KHiLink kSymbol         Operator
KHiLink kEqual          Operator
" KHiLink kType           Type
KHiLink kBoolean        Boolean
KHiLink kNumber         Number
KHiLink kFloat          Float
KHiLink kString         String
KHiLink kComment        Comment
KHiLink kTodo           Todo
" hi def     kMisc       term=bold cterm=bold gui=bold

delcommand KHiLink
  
let b:current_syntax = "kframework"

"EOF vim: tw=78:ft=vim:ts=8

