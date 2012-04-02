
module ISSUE
	
	syntax K ::= "test1" 
	eq test1 = 'SomeLabel(.List{K}) [owise]
	rule test1 => 'OtherLabel(.List{K}) [computational]
end module
