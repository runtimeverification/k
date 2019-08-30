module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, klabel(divi)]
                 > AExp "+" AExp              [left, klabel(addi)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [klabel(lei)]
                 | "!" BExp                   [klabel(noti)]
                 > BExp "&&" BExp             [left, klabel(andi)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"                      [klabel(asigni)]
                 | "if" "(" BExp ")" Block "else" Block [klabel(ifi)]
                 | "while" "(" BExp ")" Block           [klabel(whilei)]
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}

  syntax KItem ::= #divi1(K) | #divi2(K)
  syntax KItem ::= #addi1(K) | #addi2(K)
  syntax KItem ::= #lei1(K) | #lei2(K)
  syntax KItem ::= #noti()
  syntax KItem ::= #andi(K)
  syntax KItem ::= #assigni(K)
  syntax KItem ::= #ifi(K,K)
endmodule

