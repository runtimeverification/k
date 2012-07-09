// Error when using parens as tokens

/*
java.lang.ArrayIndexOutOfBoundsException: -1
	at org.spoofax.interpreter.core.StackTracer.push(StackTracer.java:39)
	at org.strategoxt.stratego_lib.try_1_0.invoke(try_1_0.java)
	at k3parser.lib.lifted54.invoke(lifted54.java:20)
	at org.strategoxt.lang.compat.override.performance_tweaks.s_0.invoke(
s_0.java)
	at org.strategoxt.lang.SRTS_all.invoke(SRTS_all.java)
	at org.strategoxt.lang.compat.override.performance_tweaks.s_0.invoke(
s_0.java)
	at org.strategoxt.lang.SRTS_all.invoke(SRTS_all.java)
	at org.strategoxt.lang.compat.override.performance_tweaks.s_0.invoke(
s_0.java)
	at org.strategoxt.lang.SRTS_all.invoke(SRTS_all.java)
	at org.strategoxt.lang.compat.override.performance_tweaks.s_0.invoke(
s_0.java)
	at org.strategoxt.lang.SRTS_all.invoke(SRTS_all.java)
	at org.strategoxt.lang.compat.override.performance_tweaks.s_0.invoke(
s_0.java)
	at org.strategoxt.lang.SRTS_all.map(SRTS_all.java)
	at org.strategoxt.lang.SRTS_all.invoke(SRTS_all.java)
	at org.strategoxt.lang.compat.override.performance_tweaks.s_0.invoke(
s_0.java)
	at org.strategoxt.lang.SRTS_all.invoke(SRTS_all.java)
	at org.strategoxt.lang.compat.override.performance_tweaks.s_0.invoke(
s_0.java)
	at org.strategoxt.lang.compat.override.performance_tweaks.topdown_1_0_
override.invoke(topdown_1_0_override.java)
	at k3parser.lib.mydisambiguate_0_1.invoke(mydisambiguate_0_1.java:54)
	at k3parser.lib.just$Fine$Rule_0_1.invoke(just$Fine$Rule_0_1.java:21)
	at k3parser.lib.java$Parse$String$Rules_0_0.invoke(java$Parse$String$
Rules_0_0.java:56)
	at org.strategoxt.lang.Context.invokeStrategyCLI(Context.java)
	at k3parser.KParser.ParseKRuleString(KParser.java:295)
	at k3.basic.Rule.parse(Rule.java:36)
	at k3.basic.Definition.parseRules(Definition.java:908)
	at main.KompileFrontEnd.maudify(KompileFrontEnd.java:555)
	at main.KompileFrontEnd.kompile(KompileFrontEnd.java:133)
	at main.Main.main(Main.java:17)
Error: Cannot parse rule: -1 at: (10,2,10,54) in file: /home/kirarinsnow/
k-framework/trunk/dist/include/builtins/bool.k

*/


module LAZYK-SYNTAX
   syntax Program  ::= "PROGRAM" CCExpr
                     | "PROGRAM"

   syntax CCExpr   ::= CCExpr Expr
                     | Expr
		   
   syntax Expr     ::= "!"
                     | ExprPrime
 
//   syntax IotaExpr ::= "!"
//                     | ExprPrime

   syntax ExprPrime  ::= "k"
                       | "s"
                       | "j"
                       | NonemptyJotExpr
                       | ">" Expr Expr
//                       | "*" IotaExpr IotaExpr
                       | "(" CCExpr ")"          // <-
                       | "(" ")"                 // <-

   syntax NonemptyJotExpr ::= NonemptyJotExpr "z"
                            | NonemptyJotExpr "o"
                            | "z"
                            | "o"

endmodule

module LAZYK
  imports LAZYK-SYNTAX
  configuration <k> $PGM:Program </k>
  syntax KResult ::= Program
endmodule
