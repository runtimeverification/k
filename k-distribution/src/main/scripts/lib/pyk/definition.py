#!/usr/bin/env python3

import sys
import subprocess

from .kast      import *
from .kastManip import *

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

def minimizeDefinition(definition, rulesList):
    new_definition = keepDefinitionModulesOnly(definition)
    new_definition = keepSentences(new_definition, lambda sent: ruleHasId(sent, rulesList))
    used_labels    = collectKLabelsFromRules(new_definition)
    new_definition = keepSentences(new_definition, lambda sent: syntaxHasKLabel(sent, used_labels))
    return new_definition
