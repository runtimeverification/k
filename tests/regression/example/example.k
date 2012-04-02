
module COMMON 
  syntax Bag ::= "start" | "good" | "bad"
  declare test : Int -> K
  rule test(I:Int) => I %Int 5




  rule start => <k> test(7) </k>
  rule <k> 2 </k> => good
  rule <k> I:Int </k> => bad when I =/=Int 2
end module
