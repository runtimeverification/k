
module EXAMPLE 
	
        
	syntax Exp ::= Id  | let Ids = Exps in { Stmts }

/*
   syntax Exp ::= let = in { }
   macro (let = in {}) = (let .List{","} = .List{","} in {.List{""}})

   syntax Exp ::= let Ids = in { }
   macro (let X:Ids = in {}) = (let X:Ids = .List{","} in {.List{""}})

   syntax Exp ::= let = Exps in { }
   macro (let = X:Exps in {}) = (let .List{","} = X:Exps in {.List{""}})

   syntax Exp ::= let = in { Stmts }
   macro (let = in {X:Stmts}) = (let .List{","} = .List{","} in {X:Stmts})

   syntax Exp ::= let Ids = Exps in { }
   macro (let X:Ids = Y:Exps in {}) = (let X:Ids = Y:Exps in {.List{""}})

   syntax Exp ::= let Ids = in { Stmts }
   macro (let X:Ids = in { Y:Stmts }) = (let X:Ids = .List{","} in {Y:Stmts})

   syntax Exp ::= let = Exps in { Stmts }
   macro (let = X:Exps in { Y:Stmts }) = (let .List{","} = X:Exps in { Y:Stmts })

*/    

        syntax Ids ::= List{Id,","}
        syntax Exps ::= List{Exp,","}

        syntax Stmt ::= nop ;
        syntax Stmts ::= List{Stmt,""}
        
end module
