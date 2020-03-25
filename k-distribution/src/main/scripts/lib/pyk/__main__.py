#!/usr/bin/env python3

import argparse
import tempfile
import os.path as path

from .         import *
from .graphviz import *

pykArgs = argparse.ArgumentParser()
pykArgs.add_argument('kompiled-dir', type = str, help = 'Kompiled directory for definition.')

pykCommandParsers = pykArgs.add_subparsers(dest = 'command')

kastArgs = pykCommandParsers.add_parser('parse', help = 'Parse an input program.')
kastArgs.add_argument('-i', '--input',  type = argparse.FileType('r'), default = '-')
kastArgs.add_argument('-o', '--output', type = argparse.FileType('w'), default = '-')
kastArgs.add_argument('-f', '--from', default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])
kastArgs.add_argument('-t', '--to',   default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])
kastArgs.add_argument('kArgs', nargs='*', help = 'Arguments to pass through to K invocation.')

krunArgs = pykCommandParsers.add_parser('run', help = 'Run an input program.')
krunArgs.add_argument('-i', '--input',  type = argparse.FileType('r'), default = '-')
krunArgs.add_argument('-o', '--output', type = argparse.FileType('w'), default = '-')
krunArgs.add_argument('-f', '--from', default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])
krunArgs.add_argument('-t', '--to',   default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])
krunArgs.add_argument('kArgs', nargs='*', help = 'Arguments to pass through to K invocation.')

kproveArgs = pykCommandParsers.add_parser('prove', help = 'Prove an input specification.')
kproveArgs.add_argument('-i', '--input',  type = argparse.FileType('r'), default = '-')
kproveArgs.add_argument('-o', '--output', type = argparse.FileType('w'), default = '-')
kproveArgs.add_argument('-t', '--to',   default = 'pretty', choices = ['pretty', 'json', 'kast', 'binary', 'kore'])
kproveArgs.add_argument('kArgs', nargs='*', help = 'Arguments to pass through to K invocation.')

graphImportsArgs = pykCommandParsers.add_parser('graph-imports', help = 'Graph the imports of a given definition.')

coverageImportsArgs = pykCommandParsers.add_parser('coverage', help = 'Convert coverage file to human readable log.')
coverageImportsArgs.add_argument('coverage-file', type = argparse.FileType('r'), help = 'Coverage file to build log for.')

minimizerArgs = pykCommandParsers.add_parser('minimize', help = 'Minimize a definition.')
minimizerArgs.add_argument('coverage-file', type = argparse.FileType('r'), help = 'Coverage file with rule list to keep.')

def definitionDir(kompiledDir):
    return path.dirname(path.abspath(kompiledDir))

if __name__ == '__main__':
    returncode = 0
    args = vars(pykArgs.parse_args())
    kompiled_dir = args['kompiled-dir']

    if args['command'] in [ 'parse' , 'run' , 'prove' ]:
        inputFile = args['input'].name
        if inputFile == '<stdin>':
            with tempfile.NamedTemporaryFile(mode = 'w') as tempf:
                tempf.write(args['input'].read())
                inputFile = tempf.name
        definition_dir = definitionDir(kompiled_dir)
        if args['command'] == 'parse':
            (returncode, stdout, stderr) = kast(definition_dir, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
            args['output'].write(stdout)
        elif args['command'] == 'run':
            (returncode, stdout, stderr) = krun(definition_dir, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
            args['output'].write(stdout)
        elif args['command'] == 'prove':
            (returncode, stdout, stderr) = kprove(definition_dir, inputFile, kArgs = ['--input', args['from'], '--output', args['to']] + args['kArgs'])
            args['output'].write(stdout)

    elif args['command'] == 'graph-imports':
        returncode = 0 if graphvizImports(kompiled_dir + '/parsed') and graphvizImports(kompiled_dir + '/compiled') else 1

    elif args['command'] == 'coverage-log':
        json_definition = removeSourceMap(readKastTerm(kompiled_dir + '/compiled.json'))
        symbolTable = buildSymbolTable(json_definition)
        for rid in args['coverage_file']:
            rule = minimizeRule(stripCoverageLogger(getRuleById(json_definition, rid.strip())))
            args['output'].write('\n\n')
            args['output'].write('Rule: ' + rid.strip())
            args['output'].write('\nUnparsed:\n')
            args['output'].write(prettyPrintKast(rule, symbolTable))

    elif args['command'] == 'minimize':
        rule_list = [ line.strip() for line in args['coverage-file'].read().strip().split('\n') ]
        old_definition = readKastTerm(kompiled_dir + '/compiled.json')
        symbol_table   = buildSymbolTable(old_definition)
        new_definition = minimizeDefinition(old_definition, rule_list)
        arg['output'].write(prettyPrintKast(new_definition, symbol_table))

    args['output'].flush()

    if returncode != 0:
        _fatal('Non-zero exit code (' + str(returncode) + '): ' + str(kCommand), code = returncode)
