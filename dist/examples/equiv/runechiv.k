module RUNECHIV
    imports SUBSTITUTION

    syntax Exp ::= Id
                 | Int
                 | Bool
                 | Exp "i+" Exp [strict, klabel('_i+_)]
                 | Exp "i-" Exp [strict, klabel('_i-_)]
                 | Exp "i==" Exp [strict, klabel('_i==_)]
                 | Exp "i<" Exp [strict, klabel('_i<_)]
                 | "(" Exp ")" [bracket, klabel('(_))]
                 | "L1Exp" Id ":" Exp
		 | "Labe1Exp" Id

    syntax Stmt ::= Id ":=" Exp [strict(2), klabel('_:=_)]
                  | "skip" [klabel('skip)]
                  | Stmt ";" Stmt [left, klabel('_;_)]
                  | "if" Exp "then" Stmt "else" Stmt [strict(1), klabel
                  ('if_then_else_)]
                  | "while" Exp "do" Stmt [klabel('while_do_)]
                  | "{" Stmt "}" [bracket, klabel('{_})]
                  | "L1Stmt" Id ":" Stmt
		  | "Labe1Stmt" Id

    syntax Code ::= Exp
                  | Stmt
                  | "L1Code" Id ":" Code
		  | "Labe1Code" Id

    syntax KLabel ::= "Label1" Id

    rule <k1> 'L1Stmt_:_(I:Id,, X:Stmt) => Labe1Stmt I ~> X ...</k1> [transition]

    rule <k1> Labe1Stmt I:Id => (Label1 I)(.KList) ...</k1> [transition]

//    rule <k1> (Label1 I)(.KList) => .K ...</k1> [transition]

    syntax KResult ::= Int
                     | Bool

    rule <k1> skip => .K ...</k1>

    rule <k1> I:Id => I1:Int ...</k1> <env1>... I |-> I1 ...</env1>

    rule <k1> I1:Int i+ I2:Int => I1 +Int I2 ...</k1>

    rule <k1> I1:Int i- I2:Int => I1 -Int I2 ...</k1>

    rule <k1> I1:Int i== I2:Int => I1 ==Int I2 ...</k1>

    rule <k1> I1:Int i< I2:Int => I1 <Int I2 ...</k1>

    rule <k1> I:Id := I1:Int => .K ...</k1> <env1>... I |-> ((_:K => I1)) ...
      </env1>

    rule <k1> I:Id := I1:Int => .K ...</k1> <env1> Rho:Map ((.Map => I |-> I1
      )) </env1> when notBool (I in (keys (Rho)))

    rule <k1> S1:Stmt ; S2:Stmt => S1 ~> S2 ...</k1>

    rule <k1> if B:Bool then S1:Stmt else _:K => S1 ...</k1> when B ==Bool true

    rule <k1> if B:Bool then _:K else S2:Stmt => S2 ...</k1> when B ==Bool false

    rule <k1> while E:Exp do S:Stmt => if E then (S ; (while E do S)) else 
      skip ...</k1>

    syntax FExp ::= Id
                  | FExp "f+" FExp [strict, klabel('_f+_)]
                  | FExp "f-" FExp [strict, klabel('_f-_)]
                  | FExp "f==" FExp [strict, klabel('_f==_)]
                  | FExp "f<" FExp [strict, klabel('_f<_)]
                  | "fif" FExp "fthen" FExp "felse" FExp [strict(1), klabel
                  ('if_then_else_)]
                  | Val
                  | "fix" Id FExp [binder, klabel('fix__)]
                  | FExp FExp [seqstrict, klabel('__)]
                  | "(" FExp ")" [bracket, klabel('(_))]
                  | "L2FExp" Id ":" FExp [strict(2)]
		  | "Labe2FExp" Id

    syntax Val ::= "lambda" Id "." FExp [binder, klabel('lambda_._)]
                 | Int
                 | Bool
                 | "L2Val" Id ":" Val
		 | "Labe2" Id

    syntax KLabel ::= "Label2" Id

   // rule <k2> 'L2FExp_:_(I:Id,, X:FExp) => Labe2FExp I ~> X ...</k2> [transition]

   // rule <k2> Labe2FExp I:Id => (Label2 I)(.KList) ...</k2> [transition]

   // rule <k2> (Label2 I)(.KList) => .K ...</k2> [transition]

    syntax KResult ::= Val

    rule <k2> I1:Int f+ I2:Int => I1 +Int I2 ...</k2>

    rule <k2> I1:Int f- I2:Int => I1 -Int I2 ...</k2>

    rule <k2> I1:Int f== I2:Int => I1 ==Int I2 ...</k2>

    rule <k2> I1:Int f< I2:Int => I1 <Int I2 ...</k2>

    rule <k2> fif B:Bool fthen S1:FExp felse _:K => S1 ...</k2> when B ==Bool true

    rule <k2> fif B:Bool fthen _:K felse S2:FExp => S2 ...</k2> when B ==Bool false

    rule <k2> (lambda X:Id . E:FExp) V:Val => E [ V / X ] ...</k2>

    rule <k2> fix X:Id E:FExp => E [ (fix X E) / X ] ...</k2>

    configuration
        <aggregation>
                <first>
                    <t1>
                        <k1>
                            $PGM:K
                        </k1>
                        <env1>
                            .Map
                        </env1>
                    </t1>
                </first>
            <second>
                <t2>
                    <k2>
                        $PGM2:K
                    </k2>
                </t2>
            </second>
        </aggregation>

      syntax KResult ::= "Success1" | "Success2"

      rule <k1> .K </k1> <env1>... _:Id |-> (R1:KResult => Success1) ...</env1>
      	   <k2> R2:KResult => Success2 </k2> when R1 ==K R2 [transition]

//      rule #freezer (X:Id => 1)

	// rule
        //    <k2>
	//          L2FExp YL:Id : X:K ~> (#freezer (Y:K f+ HOLE))(.KList) => 
	//          L2FExp YL : (Y f+ X)
        //    </k2>



      rule 
           <k2>
                L2FExp L1:Id : N:Int ~> (#freezer (lambda X:Id . (fif (N1:Int
                  f== 0) fthen X felse (((fix F:Id (lambda
                  Y:Id . (lambda X . (fif (Y f== 0) fthen X felse
                  ((F (Y f- 1)) (L2FExp L1 : (X f+ Y))))))) (N1 f- 1)) (
                  L2FExp L1 : (X f+ N1))))) HOLE)(.KList) => .K
           </k2>
      	   <t1>
      	   <k1>
      		((Label1 YP:Id)(.KList) ~>
      		   (while (I:Id i< NName:Id) do (((S:Id := (S i+ I)) ; (
                    I := (I i+ 1))) ; (Labe1Stmt YP)))) => .K
           </k1>
      	   <env1>... NName |-> NP:Int
      	   	     I |-> IP:Int
      	             S |-> SPB:Int
           ...</env1>
      	   </t1>
//      	   when //(N1 ==Int N -Int 1) ==Bool true // andBool
      // 	   // SPE = (N + ... + NP - 1)
      // 	   // SPB = (1 + ... + I - 1)
//                SPE ==Int ((N +Int NP -Int 1) *Int (IP -Int 1)) /Int 2 andBool 
//                (SPB *Int 2 ==Int (IP *Int (IP -Int 1))) [symbolic-kompile]

endmodule
