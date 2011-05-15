# 
# usage: cat <bf-program>.bf | python parser.py > <bf-program>.k
# -----------------------------------------------------------------------------

import sys

s = sys.stdin.read()
x = 0
y = 0


print """
load befunge-compiled
mod BEFUNGE-TEST is
	including BEFUNGE .
	
	--- Programs
  	op pProgram : -> KProperLabel .
	eq pProgram = 
"""

print "injectM( __((.).Map,((.).Map "
for line in s.splitlines():
	x = 0
	for c in line:
		if c == '\\':
			c = '\\\\'
		if c == '"':
			c = '\\"'
		print "\t'coord`(_`,_`)(Int %(x)d(.List{K}),, Int %(y)d(.List{K})) |-> String \"%(c)s\"(.List{K})" % {'x': x, 'y': y, 'c': c}
		#print x, y, c
		x += 1
	y += 1
print ")))"

print """
.
endm
rew eval(pProgram(.List{K})) .
q

"""
