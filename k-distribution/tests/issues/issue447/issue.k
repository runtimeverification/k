// Copyright (c) 2012-2015 K Team. All Rights Reserved.
module ISSUE

syntax AExp ::= Int
              // > "(" AExp ")" [bracket]
              // > "-" AExp [strict]
              // > AExp "*" AExp [left, seqstrict]
              // | AExp "/" AExp [left, seqstrict]
              // > AExp "+" AExp [left, seqstrict]
              // | AExp "-" AExp [left, seqstrict]
              // > "~" AExp [strict]
              // > AExp "^" AExp [left, seqstrict]
              // > AExp "&" AExp [left, seqstrict]
              // > AExp "|" AExp [left, seqstrict]

syntax BExp ::= Bool
              // > AExp "=" AExp [seqstrict]
              // > BExp "=" BExp [left, seqstrict]
              // > "(" BExp ")" [bracket]
              // > "not" BExp [strict]
              // > BExp "and" BExp [strict]
              // > BExp "or" BExp [strict]

syntax Block ::= "{" List{Stmt, ""} "}" [seqstrict]

syntax Stmt ::= Id ":=" AExp ";" [strict(2)]
              // > Id ":=" BExp ";" [strict(2)]
              > Block
              // > "if" BExp Stmt Stmt [strict(1)]
              // > "while" BExp "do" Stmt
              // > "repeat" Stmt "while" BExp
              // > "for" Stmt BExp Stmt Stmt

endmodule

