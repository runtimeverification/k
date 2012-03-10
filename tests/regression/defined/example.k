module ISSUE 
        syntax Exp ::= #Int 
        declare _/_ : Exp Exp -> Exp
        define I1:#Int / I2:#Int => I1 /Int I2 when I2 =/=Bool 0

        declare _*_ : Exp Exp -> Exp
        define 0 * _:Exp => 0
        define _:Exp * 0 => 0
        define I1:#Int * I2:#Int => I1 *Int I2

        syntax K ::= test1
	rule test1 => 0 * (5 / 0) [anywhere]
end module
