
module IMPPP-SYNTAX
  syntax AExp ::= Id | Int
                | AExp "+" AExp    [prec(33) gather (E e) strict]
                | AExp "/" AExp    [prec(31) gather (E e) strict]
  syntax BExp ::= #Bool
                | AExp "<=" AExp   [prec(37) seqstrict latex("{#1}\leq{#2}")]
                | "not" BExp       [prec(53) strict]
                | BExp "and" BExp  [prec(55) strict(1)]
  syntax Stmt ::= "skip"
                | Id ":=" AExp    [prec(80) strict(2)]
                | Stmt ";" Stmt    [prec(100) gather(e E)]
                | "if" BExp
                  "then" Stmt
                  "else" Stmt      [prec(85) strict(1)]
                | "while" BExp
                  "do" Stmt        [prec(85)]
  syntax Ids ::= List{Id,","}

  syntax AExp ::= String
                | "++" Id               [prec(0)]
                | "read" "(" ")"
  syntax AExps ::= List{AExp,","}     [strict]

  syntax Stmt ::= "print" "(" AExps ")"  [strict]
                | "halt"
                | "spawn" Stmt           [prec(90)]
                | "{" "}"
                | "{" Stmt "}"           [gather(&)]
                | "var" Ids              [prec(70)]
end module


module IMPPP
  imports IMPPP-SYNTAX
  configuration
    <T color="yellow">
      <threads color="orange">
        <thread multiplicity="*" color="red">
          <k color="green"> $PGM:K </k>
          <env color="LightSkyBlue"> .Map </env>
        </thread>
     </threads>
     <br/>
     <store color="white"> .Map </store>
     <nextLoc color="gray"> 0 </nextLoc>
     <in color="magenta"> $IN:List </in>
     <out color="Orchid"> .List </out>
    </T>
  syntax KResult ::= Int | #Bool


  rule <k> X:Id => I ...</k>
       <env>... X |-> N:Nat ...</env>
       <store>... N |-> I:Int ...</store>


  rule I1:Int + I2:Int => I1 +Int I2
  rule I1 / I2 => I1 /Int I2 when I2 =/=Bool 0


  rule I1 <= I2 => I1 <=Int I2
  rule not T:#Bool => notBool T
  rule true and B:BExp => B
  rule false and B => false


  rule skip => .


  rule <k> X := I => . ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store>

// Sequential composition

  rule S1:K ; S2:K => S1 ~> S2  [structural]

// Conditional

  rule if  true then S1 else _  => S1
  rule if false then _  else S2 => S2

// While loop

  rule <k> while B do S:K => if B then S ; while B do S else {} ...</k>


//  syntax Val ::= String
  syntax KResult ::= String
  rule Str1:String + Str2:String => Str1 +String Str2

  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>
  rule <k> read() => I ...</k>
       <in> ListItem(I) => . ...</in>

  syntax Printable ::= Int | String
  rule <k> print(P:Printable,AEs:AExps => AEs) ...</k>
       <out>... . => ListItem(P) </out>
  rule print(.AExps) => .  [structural]

  rule <threads>... <k> halt ...</k> ...</threads> => <threads> .Bag </threads>

  rule <k> spawn S => . ...</k> <env> Rho </env>
       (. => <k> S </k> <env> Rho </env>)

  rule <thread>... <k> .K </k> ...</thread> => .  [structural]

  rule {} => .  [structural]
  rule <k> {S} => S ~> env(Rho) ...</k> <env> Rho:Map </env>  [structural]

  rule <k> var (X,Xl => Xl:Ids) ...</k>
       <env> Rho => Rho[N/X] </env>
       <store>... . => N |-> 0 ...</store>
       <nextLoc> N => N +Int 1 </nextLoc>
  rule var .Ids => .  [structural]

  syntax K ::= "env" "(" Map ")"
  rule (env(_) => .) ~> env(_)  [structural]
  rule <k> env(Rho) => . ...</k> <env> _ => Rho </env>  [structural]

  syntax K ::= sum-1
  rule sum-1 => '_;_('var_('_`,_(#id_("n"),,'_`,_(#id_("s"),,.Ids))),,'_;_('_:=_(#id_("n"),,10),,'_;_('_:=_(#id_("s"),,0),,'_;_('while_do_('not_('_<=_(#id_("n"),,0)),,'`{_`}('_;_('_:=_(#id_("s"),,'_+_(#id_("s"),,#id_("n"))),,'_:=_(#id_("n"),,'_+_(#id_("n"),,-1))))),,'print`(_`)('_`,_(#id_("s"),,.AExps))))))

  syntax Bag ::= good

  rule good =>
  <T> <nextLoc> 2 </nextLoc> <in> (.).List </ in > 
    <out> ListItem(55) </out> <threads> (.).Bag </threads> 
    <store> 0 |-> 0 1 |-> 55 </store>
  </T>

end module
