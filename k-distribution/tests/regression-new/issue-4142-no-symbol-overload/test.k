module TEST
  imports DOMAINS

  syntax LVal ::= lv(Int) | lv(Id)
  syntax RVal ::= rv(Int)
  syntax Val  ::= LVal | RVal

  syntax Exp  ::= Int
                | Id
                | Val
                | "(" Exp ")" [bracket]
                > left:
                  Exp "," Exp [group(comma)]

  syntax RVals ::= RVal           [overload(arg),  group(assignExp), symbol(rval), avoid]
                 | RVals "," RVal [overload(exps), group(assignExp)]

  syntax Vals  ::= Val            [overload(arg),  group(assignExp), symbol(val),  avoid]
                 | Vals "," Val   [overload(exps), group(assignExp)]

  syntax Exps  ::= Exp            [overload(arg),  group(assignExp), symbol(exp),  avoid]
                 | Exps "," Exp   [overload(exps), group(assignExp)]

  syntax Exps ::= Vals
  syntax Vals ::= RVals

  syntax priority assignExp > comma

  syntax KItem ::= "rvals"
                 | "vals"
                 | "exps"

  configuration
    <k> $PGM:Exps </k>

  rule _:RVals => rvals
  rule _:Vals  => vals
  rule _:Exps  => exps  [owise]
endmodule
