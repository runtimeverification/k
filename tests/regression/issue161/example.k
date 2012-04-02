
module COMMON 
end module

module ISSUE134A 
	imports COMMON
	op test1 : -> KLabel
	eq test1 = 'SomeLabel
end module


module ISSUE134B 
	imports COMMON
	op test2 : -> KLabel
	eq test2 = 'SomeLabel
end module

module ISSUE134 
	imports ISSUE134A
	imports ISSUE134B
end module
