
module ISSUE
        sort C

	op vpair : K K -> C [metadata "hybrid=() strict=()"] 

        syntax K ::= a
        syntax KResult ::= b	

        syntax K ::= test C  [strict]

        syntax Bag ::= startBag | goodBag

        rule startBag =>  <k> test vpair(a,a) </k>
        rule <k> test vpair(b,b) <_/k> => goodBag 

        rule <k> a => b <_/k>
     
end module
