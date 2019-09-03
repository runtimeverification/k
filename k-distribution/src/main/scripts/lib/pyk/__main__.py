#!/usr/bin/env python3

import argparse
import tempfile

from .         import *
from .graphviz import *

pykArgs = argparse.ArgumentParser()

pykArgs.add_argument('command' , choices = ['parse', 'run', 'prove', 'graph-imports'])

pykArgs.add_argument('-d', '--definition')

pykArgs.add_argument('-i', '--input',  type = argparse.FileType('r'), default = '-')
pykArgs.add_argument('-o', '--output', type = argparse.FileType('w'), default = '-')

pykArgs.add_argument('-f', '--from', default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])
pykArgs.add_argument('-t', '--to',   default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])

pykArgs.add_argument('kArgs', nargs='*', help = 'Arguments to pass through to K invocation.')

args = vars(pykArgs.parse_args())

print(args)

inputFile = args['input'].name
if inputFile == '-':
    with tempfile.NamedTemporaryFile(mode = 'w') as tempf:
        tempf.write(args['input'].read())
        inputFile = tempf.name

definition = args['definition']
if args['command'] == 'parse':
    (returncode, stdout, stderr) = kast(definition, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
elif args['command'] == 'run':
    (returncode, stdout, stderr) = krun(definition, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
elif args['command'] == 'prove':
    (returncode, stdout, stderr) = kprove(definition, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
elif args['command'] == 'graph-imports':
    returncode = 0 if graphvizImports(definition + '/parsed') and graphvizImports(definition + '/compiled') else 1
    stdout = ''

args['output'].write(stdout)

if returncode != 0:
    _fatal('Non-zero exit code (' + str(returncode) + ': ' + str(kCommand), code = returncode)
