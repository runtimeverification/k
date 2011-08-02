
kmod KLABEL-ISSUE is 
    syntax Exp ::= #Int
                 | { List{Field} }

    syntax List{Field} ::= #Id = Exp --- not converted to a K label
         | List{Field} , List{Field}  [strict hybrid assoc comm prec 70]

    syntax K ::= Exp

    syntax #Id ::= a | b | c
    syntax Exp ::= test01

    macro test01 = { a = 10 }
endkm
