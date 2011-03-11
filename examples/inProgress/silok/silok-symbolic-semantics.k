require silok-programs

kmod SILOK-SYMBOLIC-SEMANTICS is including SILOK-SYNTAX + SILOK-PROGRAMS + K + PL-INT + PL-ID

 
  syntax K ::= B | restore ( Map ) | lvars | gvars 
  	       | Procs | Pgm | Smb | IdInt | ListId
  syntax IntBot ::= Int | bot
  syntax Builtins ::= IntBot
  syntax KResult ::= IntBot | Id

  syntax Bool ::= IntBot !=Int IntBot [ditto]
  rule I:Int !=Int bot => true [structural]
  rule bot !=Int I:Int => true [structural]
  rule bot !=Int bot => false [structural]


  syntax Smb ::= IdBtm ==Smb IdBtm [comm prec 40]  
		 | Smb andSmb Smb [comm assoc id: epsilon prec 41]
		 | epsilon

  syntax Smb ::=  Smb andSt Smb [assoc id: epsilon prec 41] 


  syntax K ::= wklist ( List{K} )

  syntax List{K} ::= listK ( ListId )

  rule listK(Id:Id,LI:ListId) => Id ,, listK(LI) 
       if LI =/=Bool .ListId [structural]
  rule listK(Id) => Id [structural]
  rule listK(.ListId) => .List{K} [structural]


  syntax IdBtm ::= IdInt | btm
  syntax IdInt ::= K `- Int [prec 30]
  syntax Id ::= fst IdInt [prec 35]
  syntax Int ::= snd IdInt [prec 35]
  eq fst Id:Id - I:Int = Id
  eq snd Id - I = I

***(  
  syntax Smb ::= IdBtm ==Smb IdBtm [comm prec 40]  
		 | Smb andSmb Smb [comm assoc id: epsilon prec 41]
		 | Smb andSt Smb [assoc id: epsilon prec 41] 
		 | epsilon
***)

  eq XI:IdInt ==Smb YI:IdInt andSmb YI ==Smb ZI:IdInt = XI ==Smb ZI
  
  syntax Bool ::= Smb \=Smb Smb [prec 45]
  eq Phi1:Smb andSmb Phi2:Smb \=Smb Phi1 = true
  eq Phi1 \=Smb Phi2 = false [owise]  

  syntax Bool ::= Smb X=Smb Smb [prec 45]
  eq Phi1 X=Smb Phi2 = notBool(Phi1 \=Smb Phi2)

  syntax Smb ::= andStV0EqBtm List{K}
  eq andStV0EqBtm .List{K} = epsilon
  eq andStV0EqBtm (K:K ,, Ks:List{K}) = K - 0 ==Smb btm andSt andStV0EqBtm Ks

  syntax Smb ::= Smb andStList List{K} `- Map `=btm
  eq Phi:Smb andStList .List{K} - Map:Map =btm = Phi
  eq Phi andStList K:K,,L - ( K |-> I Map ) =btm 
     = 
     (K - I ==Smb btm) andSt (Phi andStList L - (K |-> I Map) =btm)

  syntax Map ::= inc List{K} from Map
  eq inc .List{K} from Map = Map
  eq inc K,,L from (K |-> I Map) = inc L from (K |-> (I +Int 1) Map)

  syntax Smb ::= Smb `[ Map `, Map `, List{K} `]
  eq Phi [ Map1:Map, Map2:Map, .List{K} ] = Phi
  eq Phi [ (K |-> I1:Int Map1) , (K |-> I2:Int Map2) , K,,L ] 
     = (Phi andSt K - I1 ==Smb K - I2)  
       [ (K |-> I1 Map1) , (K |-> I2 Map2) , L ] 

  syntax Smb ::= st2smb `( Smb `)
  eq st2smb (epsilon) = epsilon
  eq st2smb ( XI ==Smb YI andSt Phi ) = XI ==Smb YI andSmb st2smb(Phi)

  configuration <T> 
                  <k> .K </k>
                  <state> .K </state>
		  <pgm> .Map </pgm>
		  <ci> .Map </ci>
                </T>

  syntax Bag ::= run ( KLabel )
  rule run (KL:KLabel) => 
       <T_> 
       	   <k> KL(.List{K})~>main </k>
	<_/T> [structural]

  rule <k> (gvars: LG:ListId  lvars: LL:ListId { Ps:Procs}) => Ps <_/k>
       <state> . => andStV0EqBtm listK(LG,LL) </state>
       <ci> S:Map => S[0/listK(LG,LL)] </ci>
       <pgm> .Map => ( gvars|->wklist(listK(LG)) lvars|->wklist(listK(LL)))</pgm>


  rule ( Ps1:Procs Ps2:Procs ) => Ps1 ~> Ps2
  rule <k> ( P:ProcId :: B:B ) => . <_/k>
       <pgm_> .Map => P|->B <_/pgm>

  rule B1:B;B2:B => B1~>B2  
  rule <k> B1+B2 => B1 <_/k>
  rule <k> B1+B2 => B2 <_/k>

  rule <k> X:Id:=Y:Id => . <_/k>
       <state> Phi:Smb => Phi andSt X-(I +Int 1) ==Smb Y-J </state>
       <ci_> X |-> (I:Int => I +Int 1) Y |-> J:Int <_/ci>
  rule <k> X:Id :=new => . <_/k>
       <ci_> X|->(I => I +Int 1) <_/ci>

  rule <k> [X=Y]B:B => B <_/k>
       <state> Phi </state>
       <ci_> X|->I Y|->J <_/ci>
  if st2smb(Phi) \=Smb (X-I ==Smb Y-J)
  rule <k> [X/=Y]B:B => B <_/k>
       <state> Phi </state>
       <ci_> X|->I Y|->J <_/ci>
  if st2smb(Phi) X=Smb (X-I ==Smb Y-J)
  
  rule <k> P:ProcId => B~>restore(CI) <_/k>
       <state> Phi => Phi andStList L - CI =btm </state> ---todo
       <ci> CI:Map => (inc L from CI) </ci> ---todo
       <pgm_> lvars|->wklist(L:List{K}) P|->B:B <_/pgm>
  rule <k> restore(CI':Map) => . <_/k>
       <state> Phi => Phi[CI, CI', L] </state> ---todo
       <ci> CI => (inc L from CI) </ci> ---todo
       <pgm_> lvars|->wklist(L:List{K}) <_/pgm>

endkm
