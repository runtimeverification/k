load system-F-compiled

rewrite [[ 'pgm001 ]] .
rewrite [[ 'pgm002 ]] .
rewrite [[ 'pgm003 ]] .
rewrite [[ 'pgm004 ]] .
rewrite [[ 'pgm005 ]] . --- should fail
rewrite [[ 'pgm006 ]] .

rewrite [[ 'compose ]] .
rewrite [[ 'compose2 ]] .
rewrite [[ 'lambdaxx ]] .
rewrite [[ 'ctrue ]] .
rewrite [[ 'cfalse ]] .
rewrite [[ 'cnot ]] .
