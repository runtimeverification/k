
module NON-K-STRICTNESS
    syntax Exp ::= Int | Float
                 | Exp "+" Exp [metadata "strict=() type-strict=()"]
                 | Exp "*" Exp [metadata "seqstrict=() type-strict=()"]
                 | Exp "/" Exp [metadata "seqstrict=(2 1) type-strict=()"]
                 | "integer" "(" Exp ")" [metadata "seqstrict=()  type-strict=()"]
                 | "float" "(" Exp ")" [metadata "seqstrict=()  type-strict=()"]


   syntax Pgm ::= "eval" "(" Exp ")" [metadata "type-strict=()"]

   syntax Type ::= "int" | "float" | "correct" | "typeError" "(" K ")"
   syntax Exp ::= Type 

   syntax KResult ::= Int | Float

   syntax TypeResult ::= Type

   configuration <k> .K </k> <type> .K </type> 

   rule <type> I:Int => int ...</type>
   rule <type> F:Float => float ...</type>
   rule <type> L:KLabel(int,, int) => int ...</type>
      when L ==KLabel '_+_ orBool L ==KLabel '_*_ orBool L ==KLabel '_/_
   rule <type> L:KLabel(float,, float) => float ...</type>
      when L ==KLabel '_+_ orBool L ==KLabel '_*_ orBool L ==KLabel '_/_
   rule <type> integer(T:Type) => int ...</type>
      when T ==K int orBool T ==K float 
   rule <type> float(T:Type) => float ...</type>
      when T ==K int orBool T ==K float 


// Error handling
   rule <type> L:KLabel(int,, float) => typeError(L(int,, float)) ...</type>
      when L ==KLabel '_+_ orBool L ==KLabel '_*_ orBool L ==KLabel '_/_
   rule <type> L:KLabel(float,, int) => typeError(L(int,, float)) ...</type>
      when L ==KLabel '_+_ orBool L ==KLabel '_*_ orBool L ==KLabel '_/_
   
   rule <type> L:KLabel(L1:List{K},,typeError(K:K),,L2:List{K})
            => typeError(L(K)) ...</type>

   define integer(F:Float) => Float2Int(F)
   define integer(I:Int) => I

   define float(F:Float) => F
   define float(I:Int) => Int2Float(I)

   rule I1:Int + I2:Int => I1 +Int I2
   rule I1:Int * I2:Int => I1 *Int I2
   rule I1:Int / I2:Int => I1 /Int I2

   rule F1:Float + F2:Float => F1 +Float F2
   rule F1:Float * F2:Float => F1 *Float F2
   rule F1:Float / F2:Float => F1 /Float F2

   rule <type> eval(int) => correct </type>
  
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
