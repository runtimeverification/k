
kmod COMMON is
	including K 
	including K-CONTEXTS 
	including K-PROPER
endkm

kmod ISSUE284A is
	including COMMON
	op test1 : -> KLabel
	eq test1 = 'SomeLabel
endkm


kmod ISSUE284B is
	including COMMON
	op test2 : -> KLabel
	eq test2 = 'SomeLabel
endkm

kmod ISSUE284 is
	including ISSUE284A
	including ISSUE284B
endkm
