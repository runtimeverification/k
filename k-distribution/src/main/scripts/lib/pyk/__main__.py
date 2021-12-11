#!/usr/bin/env python3

import argparse
from   graphviz import Digraph
import tempfile
import os.path as path
import sys

from .      import *
from .ktool import KPrint, KProve

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

kproveArgs = pykCommandParsers.add_parser('prove', help = 'Prove an input specification (using kprovex).')
kproveArgs.add_argument('main-file', type = str, help = 'Main file used for kompilation.')
kproveArgs.add_argument('spec-file', type = str, help = 'File with the specification module.')
kproveArgs.add_argument('spec-module', type = str, help = 'Module with claims to be proven.')
kproveArgs.add_argument('--output-file', type = argparse.FileType('w'), default = '-')
kproveArgs.add_argument('--output', default = 'pretty', choices = ['pretty', 'json'])
kproveArgs.add_argument('kArgs', nargs='*', help = 'Arguments to pass through to K invocation.')

graphImportsArgs = pykCommandParsers.add_parser('graph-imports', help = 'Graph the imports of a given definition.')

coverageArgs = pykCommandParsers.add_parser('coverage', help = 'Convert coverage file to human readable log.')
coverageArgs.add_argument('coverage-file', type = argparse.FileType('r'), help = 'Coverage file to build log for.')
coverageArgs.add_argument('-o', '--output', type = argparse.FileType('w'), default = '-')

minimizeArgs = pykCommandParsers.add_parser('minimize', help = 'Output the minimized K term.')
minimizeArgs.add_argument('json-term', type = argparse.FileType('r'), help = 'JSON representation of term to minimize.')
minimizeArgs.add_argument('-o', '--output', type = argparse.FileType('w'), default = '-')
minimizeArgs.add_argument('--omit-labels', default = '', nargs = '?')

def definitionDir(kompiledDir):
    return path.dirname(path.abspath(kompiledDir))

def main(commandLineArgs, extraMain = None):
    returncode = 0
    args = vars(commandLineArgs.parse_args())
    kompiled_dir = args['kompiled-dir']

    if args['command'] in [ 'parse' , 'run' ]:
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
        kprover    = KProve(kompiled_dir, args['main-file'])
        finalState = kprover.prove(args['spec-file'], args['spec-module'], args = args['kArgs'])
        if args['output'] == 'pretty':
            args['output_file'].write(kprover.prettyPrint(finalState))
        else:
            args['output_file'].write(json.dumps({ 'format': 'KAST', 'version': 1, 'term': finalState }))
        if finalState != KConstant('#Top'):
            fatal('Proof failed!')

    elif args['command'] == 'graph-imports':
        kprinter    = KPrint(kompiled_dir)
        kDefn       = kprinter.definition
        importGraph = Digraph()
        graphFile   = kompiled_dir + '/import-graph'
        for module in kDefn['modules']:
            modName = module['name']
            importGraph.node(modName)
            for moduleImport in module['imports']:
                importGraph.edge(modName, moduleImport['name'])
        importGraph.render(graphFile)

    elif args['command'] == 'coverage':
        json_definition = removeSourceMap(readKastTerm(kompiled_dir + '/compiled.json'))
        symbolTable = buildSymbolTable(json_definition)
        for rid in args['coverage-file']:
            rule = minimizeRule(stripCoverageLogger(getRuleById(json_definition, rid.strip())))
            args['output'].write('\n\n')
            args['output'].write('Rule: ' + rid.strip())
            args['output'].write('\nUnparsed:\n')
            args['output'].write(prettyPrintKast(rule, symbolTable))

    elif args['command'] == 'minimize':
        json_definition = readKastTerm(kompiled_dir + '/compiled.json')
        symbolTable = buildSymbolTable(json_definition, opinionated = True)
        json_term = json.loads(args['json-term'].read())['term']
        if json_term == KConstant('#Top'):
            args['output'].write(prettyPrintKast(json_term, symbolTable))
        else:
            abstractLabels = [] if args['omit_labels'] is None else args['omit_labels'].split(',')
            minimized_disjuncts = []
            for d in flattenLabel('#Or', json_term):
                dMinimized = minimizeTerm(d, abstractLabels = abstractLabels)
                (dConfig, dConstraint) = splitConfigAndConstraints(dMinimized)
                if dConstraint != KConstant('#Top'):
                    minimized_disjuncts.append(KApply('#And', [dConfig, dConstraint]))
                else:
                    minimized_disjuncts.append(dConfig)
            sorted_disjunct = buildAssoc(KConstant('#Bottom'), '#Or', minimized_disjuncts)
            new_disjunct = propagateUpConstraints(sorted_disjunct)
            args['output'].write(prettyPrintKast(new_disjunct, symbolTable))

    elif extraMain is not None:
        extraMain(args, kompiled_dir)

    if returncode != 0:
        _fatal('Non-zero exit code (' + str(returncode) + '): ' + str(kCommand), code = returncode)

if __name__ == '__main__':
    sys.setrecursionlimit(15000000)
    main(pykArgs)
