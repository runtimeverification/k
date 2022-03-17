import argparse
import os.path as path
import sys
from pathlib import Path

from graphviz import Digraph

from .cli_utils import fatal, notif, warning
from .coverage import getRuleById, stripCoverageLogger
from .kast import (
    KApply,
    KAst,
    buildSymbolTable,
    flattenLabel,
    prettyPrintKast,
    readKastTerm,
)
from .kastManip import (
    minimizeRule,
    minimizeTerm,
    propagateUpConstraints,
    removeSourceMap,
    splitConfigAndConstraints,
)
from .ktool import KPrint, KProve
from .prelude import buildAssoc, mlBottom, mlTop

pykArgs = argparse.ArgumentParser()
pykArgs.add_argument('kompiled-dir', type=str, help='Kompiled directory for definition.')

pykCommandParsers = pykArgs.add_subparsers(dest='command')

kprintArgs = pykCommandParsers.add_parser('print', help='Pretty print a term.')
kprintArgs.add_argument('term', type=argparse.FileType('r'), help='Input term (in JSON).')
kprintArgs.add_argument('--minimize', default=True, action='store_true', help='Minimize the JSON configuration before printing.')
kprintArgs.add_argument('--no-minimize', dest='minimize', action='store_false', help='Do not minimize the JSON configuration before printing.')
kprintArgs.add_argument('--omit-labels', default='', nargs='?', help='List of labels to omit from output.')
kprintArgs.add_argument('--output-file', type=argparse.FileType('w'), default='-')

kproveArgs = pykCommandParsers.add_parser('prove', help='Prove an input specification (using kprovex).')
kproveArgs.add_argument('main-file', type=str, help='Main file used for kompilation.')
kproveArgs.add_argument('spec-file', type=str, help='File with the specification module.')
kproveArgs.add_argument('spec-module', type=str, help='Module with claims to be proven.')
kproveArgs.add_argument('--output-file', type=argparse.FileType('w'), default='-')
kproveArgs.add_argument('kArgs', nargs='*', help='Arguments to pass through to K invocation.')

graphImportsArgs = pykCommandParsers.add_parser('graph-imports', help='Graph the imports of a given definition.')

coverageArgs = pykCommandParsers.add_parser('coverage', help='Convert coverage file to human readable log.')
coverageArgs.add_argument('coverage-file', type=argparse.FileType('r'), help='Coverage file to build log for.')
coverageArgs.add_argument('-o', '--output', type=argparse.FileType('w'), default='-')


def definitionDir(kompiledDir):
    return path.dirname(path.abspath(kompiledDir))


def main(commandLineArgs, extraMain=None):
    returncode = 0
    args = vars(commandLineArgs.parse_args())
    kompiled_dir = Path(args['kompiled-dir'])

    if args['command'] == 'print':
        printer = KPrint(kompiled_dir)
        term = KAst.from_json(args['term'].read())
        if type(term) is dict and 'term' in term:
            term = term['term']
        if term == mlTop():
            args['output_file'].write(printer.prettyPrint(term))
        else:
            if args['minimize']:
                abstractLabels = [] if args['omit_labels'] is None else args['omit_labels'].split(',')
                minimizedDisjuncts = []
                for d in flattenLabel('#Or', term):
                    dMinimized = minimizeTerm(d, abstractLabels=abstractLabels)
                    dConfig, dConstraint = splitConfigAndConstraints(dMinimized)
                    if dConstraint != mlTop():
                        minimizedDisjuncts.append(KApply('#And', [dConfig, dConstraint]))
                    else:
                        minimizedDisjuncts.append(dConfig)
                term = propagateUpConstraints(buildAssoc(mlBottom(), '#Or', minimizedDisjuncts))
            args['output_file'].write(printer.prettyPrint(term))

    elif args['command'] == 'prove':
        kprover = KProve(kompiled_dir, args['main-file'])
        finalState = kprover.prove(Path(args['spec-file']), args['spec-module'], args=args['kArgs'])
        args['output_file'].write(finalState.to_json())
        if finalState != mlTop():
            warning('Proof failed!')

    elif args['command'] == 'graph-imports':
        kprinter = KPrint(kompiled_dir)
        kDefn = kprinter.definition
        importGraph = Digraph()
        graphFile = kompiled_dir / 'import-graph'
        for module in kDefn.modules:
            modName = module.name
            importGraph.node(modName)
            for moduleImport in module.imports:
                importGraph.edge(modName, moduleImport.name)
        importGraph.render(graphFile)
        notif('Wrote file: ' + str(graphFile))

    elif args['command'] == 'coverage':
        json_definition = removeSourceMap(readKastTerm(kompiled_dir / 'compiled.json'))
        symbolTable = buildSymbolTable(json_definition)
        for rid in args['coverage-file']:
            rule = minimizeRule(stripCoverageLogger(getRuleById(json_definition, rid.strip())))
            args['output'].write('\n\n')
            args['output'].write('Rule: ' + rid.strip())
            args['output'].write('\nUnparsed:\n')
            args['output'].write(prettyPrintKast(rule, symbolTable))

    elif extraMain is not None:
        extraMain(args, kompiled_dir)

    if returncode != 0:
        fatal('Non-zero exit code (' + str(returncode) + '): ' + str(args['command']))


if __name__ == '__main__':
    # KAST terms can end up nested quite deeply, because of the various assoc operators (eg. _Map_, _Set_, ...).
    # Most pyk operations are defined recursively, meaning you get a callstack the same depth as the term.
    # This change makes it so that in most cases, by default, pyk doesn't run out of stack space.
    sys.setrecursionlimit(10 ** 7)
    main(pykArgs)
