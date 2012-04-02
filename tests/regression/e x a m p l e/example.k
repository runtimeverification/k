
module COMMON
end module

module ISSUE284A
	imports COMMON
	op test1 : -> KLabel
	eq test1 = 'SomeLabel
end module


module ISSUE284B
	imports COMMON
	op test2 : -> KLabel
	eq test2 = 'SomeLabel
end module

module ISSUE284 is
	imports ISSUE284A
	imports ISSUE284B
end module
