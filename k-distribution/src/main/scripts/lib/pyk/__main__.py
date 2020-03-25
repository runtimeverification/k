#!/usr/bin/env python3

import argparse
import tempfile

from .         import *
from .graphviz import *

pykArgs = argparse.ArgumentParser()

pykArgs.add_argument('command' , choices = ['parse', 'run', 'prove', 'graph-imports', 'coverage-log'])

pykArgs.add_argument('-d', '--definition')

pykArgs.add_argument('-i', '--input',  type = argparse.FileType('r'), default = '-')
pykArgs.add_argument('-o', '--output', type = argparse.FileType('w'), default = '-')

pykArgs.add_argument('-f', '--from', default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])
pykArgs.add_argument('-t', '--to',   default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])

pykArgs.add_argument('kArgs', nargs='*', help = 'Arguments to pass through to K invocation.')

pykArgs.add_argument('--coverage-file', type = argparse.FileType('r'))

minimizer = argparse.ArgumentParser()
minimizerCommands = minimizer.add_subparsers()
minimizerArgs = minimizerCommands.add_parser('minimize', help = 'Minimize a definition.')
minimizerArgs.add_argument( 'definition' , type = argparse.FileType('r')                 , help = 'Definition file to minimize.'          )
minimizerArgs.add_argument( 'rules'      , type = argparse.FileType('r') , default = '-' , help = 'Coverage file with rule list to keep.' )

args = vars(pykArgs.parse_args())

print(args)
sys.exit(1)

inputFile = args['input'].name
if inputFile == '-':
    with tempfile.NamedTemporaryFile(mode = 'w') as tempf:
        tempf.write(args['input'].read())
        inputFile = tempf.name

returncode = 0
definition = args['definition']
if args['command'] == 'parse':
    (returncode, stdout, stderr) = kast(definition, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
    args['output'].write(stdout)
elif args['command'] == 'run':
    (returncode, stdout, stderr) = krun(definition, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
    args['output'].write(stdout)
elif args['command'] == 'prove':
    (returncode, stdout, stderr) = kprove(definition, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
    args['output'].write(stdout)
elif args['command'] == 'graph-imports':
    returncode = 0 if graphvizImports(definition + '/parsed') and graphvizImports(definition + '/compiled') else 1
elif args['command'] == 'coverage-log':
    json_definition = removeSourceMap(readKastTerm(definition + '/compiled.json'))
    symbolTable = buildSymbolTable(json_definition)
    for rid in args['coverage_file']:
        rule = minimizeRule(stripCoverageLogger(getRuleById(json_definition, rid.strip())))
        args['output'].write('\n\n')
        args['output'].write('Rule: ' + rid.strip())
        args['output'].write('\nUnparsed:\n')
        args['output'].write(prettyPrintKast(rule, symbolTable))

args['output'].flush()

if returncode != 0:
    _fatal('Non-zero exit code (' + str(returncode) + ': ' + str(kCommand), code = returncode)

if __name__ == '__main__':
    args = vars(minimizer.parse_args())
    ruleList = [ line.strip() for line in args['seedFile'].read().strip().split('\n') ]
    new_definition = minimizeDefinition(MCD_definition_llvm, ruleList)
    print(pyk.prettyPrintKast(new_definition, MCD_definition_llvm_symbols))
    sys.stdout.flush()
