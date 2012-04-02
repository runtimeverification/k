
module NON-K-STRICTNESS
    syntax Exp ::= Int | Float
                 | Exp "+" Exp [strict strict[type]]
---                 | Exp "+" Exp [metadata "k-strict=() type-strict=()"]
                 | Exp "*" Exp [seqstrict strict[type]]
---                 | Exp "*" Exp [metadata "k-seqstrict=() type-strict=()"]
                 | Exp "/" Exp [seqstrict(2 1) strict[type]]
---                 | Exp "/" Exp [metadata "k-seqstrict=(2 1) type-strict=()"]
                 | "integer" "(" Exp ")" [seqstrict  strict[type]]
---                 | "integer" "(" Exp ")" [metadata "k-seqstrict=()  type-strict=()"]
                 | "float" "(" Exp ")" [seqstrict strict[type]]
---                 | "float" "(" Exp ")" [metadata "k-seqstrict=()  type-strict=()"]


   syntax Pgm ::= "eval" "(" Exp ")" [type-strict]
---   syntax Pgm ::= "eval" "(" Exp ")" [metadata "type-strict=()"]

   syntax Type ::= "int" | "float" | "correct" | "typeError" "(" K ")"
   syntax Exp ::= Type 

   syntax Result ::= Int | Float
---   syntax KResult ::= Int | Float

   syntax Result[type] ::= Type
---   syntax TypeResult ::= Type

   configuration <k> .K </k> <type> .K </type> 

   rule <type> I:Int => int ...</type>
   rule <type> F:Float => float ...</type>
   rule L:KLabel(int,, int) => int 
      when L ==Bool '_+_ orBool L ==Bool '_*_ orBool L ==Bool '_/_
   rule L:KLabel(float,, float) => float 
      when L ==Bool '_+_ orBool L ==Bool '_*_ orBool L ==Bool '_/_
   rule integer(T:Type) => int 
      when T ==Bool int orBool T ==Bool float 
   rule float(T:Type) => float 
      when T ==Bool int orBool T ==Bool float 


// Error handling
   rule <type> L:KLabel(int,, float) => typeError(L(int,, float)) ...</type>
      when L ==Bool '_+_ orBool L ==Bool '_*_ orBool L ==Bool '_/_
   rule <type> L:KLabel(float,, int) => typeError(L(int,, float)) ...</type>
      when L ==Bool '_+_ orBool L ==Bool '_*_ orBool L ==Bool '_/_
   
   rule <type> L:KLabel(L1:List{K},,typeError(K:K),,L2:List{K})
            => typeError(L(K)) ...</type>

   rule integer(F:Float) => Float2Int(F)
   rule integer(I:Int) => I

   rule float(F:Float) => F
   rule float(I:Int) => Int2Float(I)

   rule I1:Int + I2:Int => I1 +Int I2
   rule I1:Int * I2:Int => I1 *Int I2
   rule I1:Int / I2:Int => I1 /Int I2

   rule F1:Float + F2:Float => F1 +Float F2
   rule F1:Float * F2:Float => F1 *Float F2
   rule F1:Float / F2:Float => F1 /Float F2

   rule eval(int) => correct
  
   rule <k> P:Pgm </k> <type> . => P </type>
   rule <k> eval(E:Exp) => E </k> <type> correct </type>


   syntax Bag ::= test1 | test2 | test3 | test4 | test5 | good | bad
  
   rule  test1 => <k> eval(3 + 5) </k> <type> .K </type>
   rule  test2 => <k> eval(3 + 5.2) </k> <type> .K </type>
   rule  test3 => <k> eval(3 + integer(5.2)) </k> <type> .K </type>
   rule  test4 => <k> eval(integer(3 + 5.2)) </k> <type> .K </type>
   rule  test5 => <k> eval(integer(float(3) + 5.2)) </k> <type> .K </type>

   rule <k> I:Int </k> <type> correct </type> => good
   rule <k> _:K </k> <type> typeError(_) </type> => bad
end module
