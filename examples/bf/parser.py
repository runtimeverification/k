# -----------------------------------------------------------------------------
# based on http://www.dabeaz.com/ply/example.html (calc.py)
# and http://magicpc.wordpress.com/2009/10/20/brainfuck-python-interpreter/
#
# The work at http://magicpc.wordpress.com/2009/10/20/brainfuck-python-interpreter/ was
# licensed under the Creative Commons Attribution-Share Alike 3.0 License.
# To view a copy of this license, visit http://creativecommons.org/licenses/by-sa/3.0
#
# The work at http://magicpc.wordpress.com/2009/10/20/brainfuck-python-interpreter/
# was written by Abd Allah Diab (mpcabd)
# Email: mpcabd ^at^ gmail ^dot^ com
# Website: http://magicpc.wordpress.com
# 
# usage: cat <bf-program>.bf | python parser.py > <bf-program>.k
# -----------------------------------------------------------------------------

import ply.lex as lex
import ply.yacc as yacc
import sys

tokens = [
    'GoLeft',
    'GoRight',
    'Print',
    'Read',
    'Increase',
    'Decrease',
    'WhileStart',
    'WhileEnd'
]

t_GoLeft = r'\<'
t_GoRight = r'\>'
t_Print = r'\.'
t_Read = r','
t_Increase = r'\+'
t_Decrease = r'\-'
t_WhileStart = r'\['
t_WhileEnd = r'\]'

def t_error(t):
    t.lexer.skip(1)

lexer = lex.lex()
    
# Build the lexer
lex.lex()

# Parsing rules

def p_start(p):
    """
    start : code
            | empty
    """
    if p[1]:
        executeStatements(p[1])

def p_empty(p):
    'empty : '
    pass

def p_code(p):
    """
    code : code statement
            | code whilestatement
            | statement
            | whilestatement
    """
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = p[1][:]
        p[0].extend([p[2]])

def p_statement(p):
    """
    statement : GoLeft
                   | GoRight
                   | Print
                   | Read
                   | Increase
                   | Decrease
    """
    if p[1] == '<':
        p[0] = ('GoLeft', None)
    elif p[1]  == '>':
        p[0] = ('GoRight', None)
    elif p[1] == '.':
        p[0] = ('Print', None)
    elif p[1] == ',':
        p[0] = ('Read', None)
    elif p[1] == '+':
        p[0] = ('Increase', None)
    elif p[1] == '-':
        p[0] = ('Decrease', None)

def p_whilestatement(p):
    'whilestatement : WhileStart code WhileEnd'
    p[0] = ('While', p[2])

# if __name__ == "__main__":
    # lex.runmain()
	
def executeStatements(tuplesList):
	if (len(tuplesList) == 0):
		print ".K",
		return
	node = tuplesList.pop(0)
	print "Seq(",
	if node[0] == 'GoLeft':
		print "%s(.List{K})" % node[0],
	elif node[0] == 'GoRight':
		print "%s(.List{K})" % node[0],
	elif node[0] == 'Print':
		print "%s(.List{K})" % node[0],
	elif node[0] == 'Read':
		print "%s(.List{K})" % node[0],
	elif node[0] == 'Increase':
		print "%s(.List{K})" % node[0],
	elif node[0] == 'Decrease':
		print "%s(.List{K})" % node[0],
	elif node[0] == 'While':
		print "%s(" % node[0],
		executeStatements(node[1])
		print ")",
	print ",,",
	executeStatements(tuplesList)
	print ")",


parser = yacc.yacc()
# for line in sys.stdin:
# # try:
s = sys.stdin.read().strip()
# except EOFError:
	# break;
# if not s:
	# continue
parser.parse(s)