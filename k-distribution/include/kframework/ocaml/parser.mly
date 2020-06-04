%{
open Constants.K
%}

%token <string> STRING KLABEL
%token KSEQ DOTK LPAREN RPAREN COMMA DOTKLIST TOKENLABEL KLABELLABEL EOF

%start top
%type <Constants.k> top

%left COMMA KSEQ

%%

top: k EOF { $1 }

k:
  kitem { $1 }
| k KSEQ k { $1 @ $3 }
| DOTK { [] }

kitem: 
  klabel LPAREN klist RPAREN { let module Def = (val Plugin.get () : Plugin.Definition) in if !Prelude.no_parse_eval then [Constants.denormalize (Constants.KApply($1, $3))] else Def.eval (Constants.KApply($1, $3)) [] }
| KLABELLABEL LPAREN klabel RPAREN { [InjectedKLabel $3] }
| TOKENLABEL LPAREN STRING COMMA sort RPAREN { [Prelude.ktoken $5 $3] }

klist:
  k { [$1] }
| klist COMMA klist { $1 @ $3 }
| klist COMMA COMMA klist { $1 @ $4 }
| DOTKLIST { [] }

klabel: KLABEL { Constants.parse_klabel $1 }

sort: STRING { Constants.parse_sort $1 }
