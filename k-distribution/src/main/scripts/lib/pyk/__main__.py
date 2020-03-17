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

args = vars(pykArgs.parse_args())

print(args)

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


mcdArgs = argparse.ArgumentParser()

mcdCommands = mcdArgs.add_subparsers()

mcdRandomTestArgs = mcdCommands.add_parser('random-test', help = 'Run random tester and check for property violations.')
mcdRandomTestArgs.add_argument( 'depth'     , type = int ,               help = 'Number of bytes to feed as random input into each run' )
mcdRandomTestArgs.add_argument( 'numRuns'   , type = int ,               help = 'Number of runs per random seed.'                       )
mcdRandomTestArgs.add_argument( 'initSeeds' , type = str , nargs = '*' , help = 'Random seeds to use as run prefixes.'                  )

mcdMinimizeArgs = mcdCommands.add_parser('minimize', help = 'Minimize Definition.')
mcdMinimizeArgs.add_argument( 'seedFile'  , type = argparse.FileType('r'), default = '-' , help = 'File containing hashes of elements to keep in definition' )

builtin_module_names = [ 'ARRAY' , 'ARRAY-CONCRETE' , 'ARRAY-IN-K' , 'ARRAY-KORE' , 'ARRAY-SYMBOLIC'
                       , 'ARRAY-SYNTAX' , 'ATTRIBUTES' , 'AUTO-CASTS' , 'AUTO-FOLLOW' , 'BASIC-K'
                       , 'BOOL' , 'BOOL-SYNTAX' , 'BUBBLE' , 'BUILTIN-ID-TOKENS' , 'BYTES'
                       , 'BYTES-CONCRETE' , 'BYTES-HOOKED' , 'BYTES-IN-K' , 'BYTES-KORE'
                       , 'BYTES-SYMBOLIC' , 'COLLECTIONS' , 'CONFIG-CELLS'
                       , 'CONFIGURATION-PRIMITIVES' , 'DEFAULT-CONFIGURATION' , 'DEFAULT-LAYOUT'
                       , 'DEFAULT-STRATEGY' , 'DEFAULT-STRATEGY-CONCRETE'
                       , 'DEFAULT-STRATEGY-SYMBOLIC' , 'DOMAINS' , 'DOMAINS-SYNTAX' , 'E-KORE'
                       , 'FFI' , 'FFI-SYNTAX' , 'FLOAT' , 'FLOAT-SYNTAX' , 'ID'
                       , 'ID-PROGRAM-PARSING' , 'ID-SYMBOLIC' , 'ID-SYNTAX' , 'INT' , 'INT-COMMON'
                       , 'INT-SYMBOLIC' , 'INT-SYNTAX' , 'K' , 'KAST' , 'K-BOTTOM-SORT' , 'KCELLS'
                       , 'K-EQUAL' , 'K-IO' , 'K-REFLECTION' , 'K-REFLECTION-SYMBOLIC' , 'KSEQ'
                       , 'KSEQ-SYMBOLIC' , 'K-SORT-LATTICE' , 'KSTRING' , 'K-TERM' , 'K-TOP-SORT'
                       , 'KVAR' , 'KVARIABLE-SYNTAX' , 'KVAR-PROGRAM-PARSING' , 'KVAR-SYMBOLIC'
                       , 'KVAR-SYNTAX' , 'LANGUAGE-PARSING' , 'LIST' , 'MAP' , 'MAP-SYMBOLIC'
                       , 'MINT' , 'MINT-SYNTAX' , 'ML-SYNTAX' , 'OUTER-KORE' , 'PROGRAM-LISTS'
                       , 'RAT' , 'RAT-COMMON' , 'RAT-KAST' , 'RAT-KORE' , 'RAT-SYMBOLIC'
                       , 'RAT-SYNTAX' , 'RECORD-PRODUCTIONS' , 'REQUIRES-ENSURES' , 'RULE-CELLS'
                       , 'RULE-LISTS' , 'RULE-TAG-SYNTAX' , 'SET' , 'SORT-K' , 'SORT-KBOTT'
                       , 'STDIN-STREAM' , 'STDOUT-STREAM' , 'STRATEGY' , 'STRATEGY-ABSTRACT'
                       , 'STRING' , 'STRING-BUFFER' , 'STRING-BUFFER-HOOKED' , 'STRING-BUFFER-IN-K'
                       , 'STRING-SYNTAX' , 'SUBSTITUTION' , 'UNIFICATION' , 'UNSIGNED-INT-SYNTAX'
                       ]

def keepDefinitionModulesOnly(kOuter):
    if pyk.isKDefinition(kOuter):
        newModules = []
        modules = { mod['name']: mod for mod in kOuter['modules'] }
        for module in modules.keys():
            if module not in builtin_module_names and not module.endswith('$SYNTAX'):
                syntaxModule = module + '$SYNTAX'
                if syntaxModule in modules:
                    newSentences = modules[syntaxModule]['localSentences'] + modules[module]['localSentences']
                    att = None if 'att' not in modules[module] else modules[module]['att']
                    newImports = [ i for i in modules[module]['imports'] if not (i == syntaxModule or i.endswith('$SYNTAX')) ]
                    newModule = pyk.KFlatModule(module, newImports, newSentences, att = att)
                    newModules.append(newModule)
                else:
                    newModules.append(modules[module])
        requires = None if 'requires' not in kOuter else kOuter['requires']
        return pyk.KDefinition(kOuter['mainModule'], newModules, requires = requires, att = att)
    return kOuter

def ruleHasId(sentence, ruleIds):
    if pyk.isKRule(sentence):
        ruleId = pyk.getAttribute(sentence, 'UNIQUE_ID')
        return ruleId is not None and ruleId in ruleIds
    return True

def syntaxHasKLabel(sentence, klabels):
    if pyk.isKProduction(sentence) and 'klabel' in sentence:
        return sentence['klabel'] in klabels
    return True

def keepSentences(kOuter, filter):
    att = None if 'att' not in kOuter else kOuter['att']
    if pyk.isKDefinition(kOuter):
        newModules = [ keepSentences(mod, filter) for mod in kOuter['modules'] ]
        requires = None if 'requires' not in kOuter else kOuter['requires']
        return pyk.KDefinition(kOuter['mainModule'], newModules, requires = requires, att = att)
    elif pyk.isKFlatModule(kOuter):
        newSentences = [ sent for sent in kOuter['localSentences'] if filter(sent) ]
        return pyk.KFlatModule(kOuter['name'], kOuter['imports'], newSentences, att = att)
    else:
        return kOuter

def collectKLabels(kast):
    labels = []
    def _collectKLabels(_kast):
        if pyk.isKApply(_kast):
            labels.append(_kast['label'])
    pyk.collectBottomUp(kast, _collectKLabels)
    return labels

def collectKLabelsFromRules(definition):
    used_labels = []
    for module in definition['modules']:
        for sentence in module['localSentences']:
            if pyk.isKRule(sentence):
                used_labels += collectKLabels(sentence['body'])
    return used_labels

def singleModule(defn):
    mainModule = defn['mainModule']
    modules = { mod['name']: mod for mod in defn['modules'] }
    moduleNames = modules.keys()
    newSentences = []
    newImports = []
    for module in defn['modules']:
        for sentence in module['localSentences']:
            if sentence not in newSentences:
                newSentences.append(sentence)
        for i in module['imports']:
            if i not in moduleNames and i not in newImports:
                newImports.append(i)
    newModuleAtt = None if 'att' not in modules[mainModule] else modules[mainModule]['att']
    newModule = pyk.KFlatModule(mainModule, newImports, newSentences, att = newModuleAtt)
    newAtt      = None if 'att'      not in defn else defn['att']
    newRequires = None if 'requires' not in defn else defn['requires']
    return pyk.KDefinition(mainModule, [ newModule ], requires = newRequires, att = newAtt)

def minimizeDefinition(definition, rulesList):
    new_definition = keepDefinitionModulesOnly(definition)
    new_definition = keepSentences(new_definition, lambda sent: not pyk.isKModuleComment(sent))
    new_definition = keepSentences(new_definition, lambda sent: not pyk.isKBubble(sent))
    new_definition = keepSentences(new_definition, lambda sent: ruleHasId(sent, ruleList))
    used_labels = collectKLabelsFromRules(new_definition)
    new_definition = keepSentences(new_definition, lambda sent: syntaxHasKLabel(sent, used_labels))
    new_definition = singleModule(new_definition)
    return new_definition

if __name__ == '__main__':
    args = vars(mcdArgs.parse_args())
    ruleList = [ line.strip() for line in args['seedFile'].read().strip().split('\n') ]
    new_definition = minimizeDefinition(MCD_definition_llvm, ruleList)
    print(pyk.prettyPrintKast(new_definition, MCD_definition_llvm_symbols))
    sys.stdout.flush()
