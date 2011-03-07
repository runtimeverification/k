require silok-programs

kmod SILOK-BASIC-SEMANTICS is including SILOK-SYNTAX + SILOK-PROGRAMS + K + PL-INT --- + K-WRAPPERS

  syntax K ::= B | restore ( Map ) | lvars | gvars | List{Id} 
  	       | Procs | Pgm 
  syntax IntBot ::= Int | bot
  syntax Builtins ::= IntBot
  syntax KResult ::= IntBot | Id

  syntax Bool ::= IntBot !=Int IntBot [ditto]
  rule I:Int !=Int bot => true [structural]
  rule bot !=Int I:Int => true [structural]
  rule bot !=Int bot => false [structural]


  syntax K ::= wklist ( List{K} )

  syntax List{K} ::= `List`{K`} ( List{Id} )

  rule List{K}(Id:Id,LI:List{Id}) => Id ,, List{K}(LI) 
       if LI =/=Bool .List{Id} [structural]
  rule List{K}(Id) => Id [structural]
  rule List{K}(.List{Id}) => .List{K} [structural]

  configuration <T> 
                  <k> .K </k>
                  <state> .Map </state>
		  <pgm> .Map </pgm>
                </T>

  syntax Bag ::= run ( KLabel )
  rule run (KL:KLabel) => 
       <T_> 
       	   <k> KL(.List{K})~>main </k>
	<_/T> [structural]


  rule ( Ps1:Procs Ps2:Procs ) => Ps1 ~> Ps2
  rule <k> ( P:ProcId :: B:B ) => . <_/k>
       <pgm_> .Map => P|->B <_/pgm>

  rule B1:B;B2:B => B1~>B2  
  rule <k> X:Id:=Y:Id => . <_/k>
       <state_> X|->(_ => I) Y|->I:Int <_/state>
  rule <k> [X=Y]B:B => B <_/k>
        <state_> X|->V:IntBot Y|->V <_/state>
  rule <k> [X/=Y]B:B => B <_/k>
       <state_> X|->V1:IntBot Y|->V2:IntBot <_/state>
  if V1 !=Int V2
  rule <k> B1+B2 => B1 <_/k>
  rule <k> B1+B2 => B2 <_/k>

endkm

