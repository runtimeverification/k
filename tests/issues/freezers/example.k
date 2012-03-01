module ISSUE 
  syntax K ::= test K
               | test1 K [strict]
               | test2 K [strict superheat]
               | nval

  syntax KResult ::= val

        
  rule test E:KItem => E ~> test HOLE when isKResult(E) =/=Bool true
  rule E:KItem ~> test HOLE => test E when isKResult(E)

  rule <k> nval => val ...</k> [supercool]

  syntax Bag ::= start | good 


  rule start => <k> test nval </k>
  rule <k> test val </k> => good 
end module
