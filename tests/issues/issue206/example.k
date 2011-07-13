
kmod ISSUE is
	including K
        sort C

	op vpair : K K -> C [metadata "hybrid=() strict=()"] 

        syntax K ::= a
        syntax KResult ::= b	

        syntax K ::= test C  [strict]

        rule test vpair(b,b) => 'SomeLabel(.List{K}) 

	syntax K ::= test1 
	rule test1 => test vpair(a,a)

        rule <k> a => b <_/k>
     
endkm
