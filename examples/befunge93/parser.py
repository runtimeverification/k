# 
# usage: cat <bf-program>.bf | python parser.py > <bf-program>.k
# -----------------------------------------------------------------------------

import sys

s = sys.stdin.read()
x = 0
y = 0
print "injectM( __(.Map,(.Map "
for line in s.splitlines():
	x = 0
	for c in line:
		if c == '\\':
			c = '\\\\'
		if c == '"':
			c = '\\"'
		print "\tcoord(inject(%(x)d)(.List{K}),, inject(%(y)d)(.List{K})) |-> inject(\"%(c)s\")(.List{K})" % {'x': x, 'y': y, 'c': c}
		#print x, y, c
		x += 1
	y += 1
print ")))"
