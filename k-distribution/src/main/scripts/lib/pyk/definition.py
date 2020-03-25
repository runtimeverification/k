#!/usr/bin/env python3

import sys
import subprocess

from .kast      import *
from .kastManip import *
from .kast      import _notif, _warning, _fatal

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
    if isKDefinition(kOuter):
        newModules = []
        modules = { mod['name']: mod for mod in kOuter['modules'] }
        for module in modules.keys():
            if module not in builtin_module_names and not module.endswith('$SYNTAX'):
                syntaxModule = module + '$SYNTAX'
                if syntaxModule in modules:
                    newSentences = modules[syntaxModule]['localSentences'] + modules[module]['localSentences']
                    att = None if 'att' not in modules[module] else modules[module]['att']
                    newImports = [ i for i in modules[module]['imports'] if not (i == syntaxModule or i.endswith('$SYNTAX')) ]
                    newModule = KFlatModule(module, newImports, newSentences, att = att)
                    newModules.append(newModule)
                else:
                    newModules.append(modules[module])
        requires = None if 'requires' not in kOuter else kOuter['requires']
        return KDefinition(kOuter['mainModule'], newModules, requires = requires, att = att)
    return kOuter

def ruleHasId(sentence, ruleIds):
    if isKRule(sentence):
        ruleId = getAttribute(sentence, 'UNIQUE_ID')
        return ruleId is not None and ruleId in ruleIds
    return True

def syntaxHasKLabel(sentence, klabels):
    if isKProduction(sentence) and 'klabel' in sentence:
        return sentence['klabel'] in klabels
    return True

def keepSentences(kOuter, filter):
    att = None if 'att' not in kOuter else kOuter['att']
    if isKDefinition(kOuter):
        newModules = [ keepSentences(mod, filter) for mod in kOuter['modules'] ]
        requires = None if 'requires' not in kOuter else kOuter['requires']
        return KDefinition(kOuter['mainModule'], newModules, requires = requires, att = att)
    elif isKFlatModule(kOuter):
        newSentences = [ sent for sent in kOuter['localSentences'] if filter(sent) ]
        return KFlatModule(kOuter['name'], kOuter['imports'], newSentences, att = att)
    else:
        return kOuter

def collectKLabels(kast):
    labels = []
    def _collectKLabels(_kast):
        if isKApply(_kast):
            labels.append(_kast['label'])
    collectBottomUp(kast, _collectKLabels)
    return labels

def collectKLabelsFromRules(definition):
    used_labels = []
    for module in definition['modules']:
        for sentence in module['localSentences']:
            if isKRule(sentence):
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
    newModule = KFlatModule(mainModule, newImports, newSentences, att = newModuleAtt)
    newAtt      = None if 'att'      not in defn else defn['att']
    newRequires = None if 'requires' not in defn else defn['requires']
    return KDefinition(mainModule, [ newModule ], requires = newRequires, att = newAtt)

def onSentences(k, f):
    if isKDefinition(k):
        return KDefinition(k['mainModule'], [onSentences(m, f) for m in k['modules']], requires = k['requires'], att = k['att'])
    if isKFlatModule(k):
        return KFlatModule(k['name'], k['imports'], [f(s) for s in k['localSentences']], att = k['att'])
    return k

def removeLog(rule):
    if not isKRule(rule):
        return rule
    logPattern = KRewrite(KVariable('LHS'), KApply('project:GeneratedTopCell', [KSequence([KApply('#logToFile', [KVariable('_1'), KVariable('_2')]), KVariable('RHS')])]))
    logMatch = match(logPattern, rule['body'])
    if logMatch is None:
        return rule
    newRuleBody = KRewrite(logMatch['LHS'], logMatch['RHS'])
    return KRule(newRuleBody, requires = rule['requires'], ensures = rule['ensures'], att = rule['att'])

def minimizeDefinition(definition, rulesList):
    new_definition = keepDefinitionModulesOnly(definition)
    new_definition = keepSentences(new_definition, lambda sent: not isKModuleComment(sent))
    new_definition = keepSentences(new_definition, lambda sent: not isKBubble(sent))
    new_definition = keepSentences(new_definition, lambda sent: not isKContext(sent))
    new_definition = keepSentences(new_definition, lambda sent: ruleHasId(sent, rulesList))
    used_labels = collectKLabelsFromRules(new_definition)
    new_definition = keepSentences(new_definition, lambda sent: syntaxHasKLabel(sent, used_labels))
    new_definition = singleModule(new_definition)
    new_definition = onSentences(new_definition, removeLog)
    new_definition = onSentences(new_definition, minimizeRule)
    return new_definition
