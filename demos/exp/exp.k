module EXP
  configuration 
    <k> $PGM:K </k>  
    <streams>
      <in stream="stdin"> .List </in> 
      <out stream="stdout"> .List </out>
    </streams>

  // Arithmetics
  syntax KResult ::= #Int 
  syntax K ::= K + K   [strict superheat] // addition
             | K * K   [strict] // multiplication
             | K / K   [strict] // division

  rule I1:#Int + I2:#Int => I1 +Int I2  
  rule I1:#Int * I2:#Int => I1 *Int I2 
  rule I1:#Int / I2:#Int => I1 /Int I2 
    if I2 =/=Bool 0 

  // Input / Output
  syntax K ::= read 
             | print K [strict]
  
  rule <k> read => I:#Int ...</k> 
       <in> ListItem(I) => .List ...</in> [supercool]
  rule <k> print I:#Int => I ...</k> 
       <out>... .List => ListItem(I) </out>

end module

