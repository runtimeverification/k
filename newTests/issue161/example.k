in funny-directory/../../../k-prelude
kmod COMMON is
	including K 
	including K-CONTEXTS 
	including K-PROPER
endkm

kmod ISSUE134A is
	including COMMON
	op test1 : -> KLabel
	eq test1 = 'SomeLabel
endkm


kmod ISSUE134B is
	including COMMON
	op test2 : -> KLabel
	eq test2 = 'SomeLabel
endkm

kmod ISSUE134 is
	including ISSUE134A
	including ISSUE134B
endkm
