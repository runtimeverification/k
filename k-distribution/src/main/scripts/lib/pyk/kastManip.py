#!/usr/bin/env python3

import sys
import subprocess

from .kast import *
from .kast import _notif, _warning, _fatal

def match(pattern, kast):
    subst = {}
    if isKVariable(pattern):
        return { pattern["name"] : kast }
    if isKToken(pattern) and isKToken(kast):
        return {} if pattern["token"] == kast["token"] else None
    if  isKApply(pattern) and isKApply(kast) \
    and pattern["label"] == kast["label"] and len(pattern["args"]) == len(kast["args"]):
        for (patternArg, kastArg) in zip(pattern["args"], kast["args"]):
            argSubst = match(patternArg, kastArg)
            subst = combineDicts(subst, argSubst)
            if subst is None:
                return None
        return subst
    if isKRewrite(pattern) and isKRewrite(kast):
        lhsSubst = match(pattern['lhs'], kast['lhs'])
        rhsSubst = match(pattern['rhs'], kast['rhs'])
        return combineDicts(lhsSubst, rhsSubst)
    if isKSequence(pattern) and isKSequence(kast) and len(pattern['items']) == len(kast['items']):
        for (patternItem, substItem) in zip(pattern['items'], kast['items']):
            itemSubst = match(patternItem, substItem)
            subst = combineDicts(subst, itemSubst)
            if subst is None:
                return None
        return subst
    return None

def onChildren(kast, effect):
    if isKApply(kast):
        return KApply(kast["label"], [ effect(arg) for arg in kast['args'] ])
    elif isKRewrite(kast):
        return KRewrite(effect(kast['lhs']), effect(kast['rhs']))
    elif isKSequence(kast):
        return KSequence([ effect(item) for item in kast['items'] ])
    return kast

def traverseBottomUp(kast, effect):
    return effect(onChildren(kast, lambda _kast: traverseBottomUp(_kast, effect)))

def traverseTopDown(kast, effect):
    return onChildren(effect(kast), lambda _kast: traverseTopDown(_kast, effect))

def collectBottomUp(kast, callback):
    callback(onChildren(kast, lambda _kast: collectBottomUp(_kast, callback)))

def collectFreeVars(kast):
    freeVars = set([])
    def addFreeVar(k):
        if isKVariable(k):
            freeVars.add(k["name"])
    collectBottomUp(kast, addFreeVar)
    return freeVars

def substitute(pattern, substitution):
    def replace(k):
        if isKVariable(k) and k["name"] in substitution:
            return substitution[k["name"]]
        return k
    return traverseBottomUp(pattern, replace)

def whereMatchingBottomUp(effect, matchPattern, pattern):
    def _effect(k):
        matchingSubst = match(matchPattern, k)
        newK = k
        if matchingSubst is not None:
            newK = effect(matchingSubst)
        return newK
    return traverseBottomUp(_effect, pattern)

def whereMatchingTopDown(effect, matchPattern, pattern):
    def _effect(k):
        matchingSubst = match(matchPattern, k)
        newK = k
        if matchingSubst is not None:
            newK = effect(matchingSubst)
        return newK
    return traverseTopDown(_effect, pattern)

def replaceKLabels(pattern, klabelMap):
    def replace(k):
        if isKApply(k) and k["label"] in klabelMap:
            return KApply(klabelMap[k["label"]], k["args"])
        return k
    return traverseBottomUp(pattern, replace)

def rewriteWith(rule, pattern):
    (ruleLHS, ruleRHS) = rule
    matchingSubst = match(ruleLHS, pattern)
    if matchingSubst is not None:
        return substitute(ruleRHS, matchingSubst)
    return pattern

def rewriteAnywhereWith(rule, pattern):
    return traverseBottomUp(pattern, lambda p: rewriteWith(rule, p))

def replaceWith(rule, pattern):
    (ruleLHS, ruleRHS) = rule
    if ruleLHS == pattern:
        return ruleRHS
    return pattern

def replaceAnywhereWith(rule, pattern):
    return traverseBottomUp(pattern, lambda p: replaceWith(rule, p))

def unsafeMlPredToBool(k):
    """Attempt to convert an ML Predicate back into a boolean expression.

    This is unsafe in general because not every ML Predicate can be represented correctly as a boolean expression.
    This function just makes a best-effort to do this.
    """
    if k is None:
        return None
    mlPredToBoolRules = [ (KApply('#Top', [])  , KToken('true', 'Bool'))
                        , (KApply('#Bottom', []) , KToken('false', 'Bool'))
                        , (KApply('#And'    , [KVariable('#V1'), KVariable('#V2')]) , KApply('_andBool_' , [KVariable('#V1'), KVariable('#V2')]))
                        , (KApply('#Or'     , [KVariable('#V1'), KVariable('#V2')]) , KApply('_orBool_'  , [KVariable('#V1'), KVariable('#V2')]))
                        , (KApply('#Not'    , [KVariable('#V1')])                   , KApply('notBool_'  , [KVariable('#V1')]))
                        , (KApply('#Equals' , [KVariable('#V1'), KVariable('#V2')]) , KApply('_==K_'     , [KVariable('#V1'), KVariable('#V2')]))
                        ]
    newK = k
    for rule in mlPredToBoolRules:
        newK = rewriteAnywhereWith(rule, newK)
    return newK

def simplifyBool(k):
    if k is None:
        return None
    simplifyRules = [ (KApply('_==K_', [KVariable('#LHS'), KToken('true', 'Bool')]), KVariable('#LHS'))
                    , (KApply('_==K_', [KToken('true', 'Bool'), KVariable('#RHS')]), KVariable('#RHS'))
                    , (KApply('_==K_', [KVariable('#LHS'), KToken('false', 'Bool')]), KApply('notBool_', [KVariable('#LHS')]))
                    , (KApply('_==K_', [KToken('false', 'Bool'), KVariable('#RHS')]), KApply('notBool_', [KVariable('#RHS')]))
                    , (KApply('notBool_', [KToken('false' , 'Bool')]), KToken('true'  , 'Bool'))
                    , (KApply('notBool_', [KToken('true'  , 'Bool')]), KToken('false' , 'Bool'))
                    , (KApply('notBool_', [KApply('_==K_'    , [KVariable('#V1'), KVariable('#V2')])]), KApply('_=/=K_'   , [KVariable('#V1'), KVariable('#V2')]))
                    , (KApply('notBool_', [KApply('_=/=K_'   , [KVariable('#V1'), KVariable('#V2')])]), KApply('_==K_'    , [KVariable('#V1'), KVariable('#V2')]))
                    , (KApply('notBool_', [KApply('_==Int_'  , [KVariable('#V1'), KVariable('#V2')])]), KApply('_=/=Int_' , [KVariable('#V1'), KVariable('#V2')]))
                    , (KApply('notBool_', [KApply('_=/=Int_' , [KVariable('#V1'), KVariable('#V2')])]), KApply('_==Int_'  , [KVariable('#V1'), KVariable('#V2')]))
                    , (KApply('_andBool_', [KToken('true', 'Bool'), KVariable('#REST')]), KVariable('#REST'))
                    , (KApply('_andBool_', [KVariable('#REST'), KToken('true', 'Bool')]), KVariable('#REST'))
                    , (KApply('_andBool_', [KToken('false', 'Bool'), KVariable('#REST')]), KToken('false', 'Bool'))
                    , (KApply('_andBool_', [KVariable('#REST'), KToken('false', 'Bool')]), KToken('false', 'Bool'))
                    , (KApply('_orBool_', [KToken('false', 'Bool'), KVariable('#REST')]), KVariable('#REST'))
                    , (KApply('_orBool_', [KVariable('#REST'), KToken('false', 'Bool')]), KVariable('#REST'))
                    , (KApply('_orBool_', [KToken('true', 'Bool'), KVariable('#REST')]), KToken('true', 'Bool'))
                    , (KApply('_orBool_', [KVariable('#REST'), KToken('true', 'Bool')]), KToken('true', 'Bool'))
                    ]
    newK = k
    for rule in simplifyRules:
        newK = rewriteAnywhereWith(rule, newK)
    return newK

def getOccurances(kast, pattern):
    occurances = []
    def addOccurance(k):
        if match(pattern, k):
            occurances.append(k)
    collectBottomUp(kast, addOccurance)
    return occurances

def flattenLabel(label, kast):
    if isKApply(kast) and kast["label"] == label:
        constraints = [ flattenLabel(label, arg) for arg in kast["args"] ]
        return [ c for cs in constraints for c in cs ]
    return [kast]

def splitConfigFrom(configuration):
    """Split the substitution from a given configuration.

    Given an input configuration `config`, will return a tuple `(symbolic_config, subst)`, where:

        1.  `config == substitute(symbolic_config, subst)`
        2.  `symbolic_config` is the same configuration structure, but where the contents of leaf cells is replaced with a fresh KVariable.
        3.  `subst` is the substitution for the generated KVariables back to the original configuration contents.
    """
    initial_substitution = {}
    _mkCellVar = lambda label: label.replace('-', '_').replace('<', '').replace('>', '').upper() + '_CELL'
    def _replaceWithVar(k):
        if isKApply(k) and isCellKLabel(k['label']):
            if len(k['args']) == 1 and not (isKApply(k['args'][0]) and isCellKLabel(k['args'][0]['label'])):
                config_var = _mkCellVar(k['label'])
                initial_substitution[config_var] = k['args'][0]
                return KApply(k['label'], [KVariable(config_var)])
        return k
    symbolic_config = traverseTopDown(configuration, _replaceWithVar)
    return (symbolic_config, initial_substitution)

def collapseDots(kast):
    def _collapseDots(_kast):
        if isKApply(_kast):
            label = _kast["label"]
            args  = _kast["args"]
            if isCellKLabel(label) and len(args) == 1 and args[0] == ktokenDots:
                return ktokenDots
            newArgs = [ arg for arg in args if arg != ktokenDots ]
            if isCellKLabel(label) and len(newArgs) == 0:
                return ktokenDots
            if len(newArgs) < len(args):
                newArgs.append(ktokenDots)
            return KApply(label, newArgs)
        elif isKRewrite(_kast):
            if _kast["lhs"] == ktokenDots:
                return ktokenDots
        return _kast
    return traverseBottomUp(kast, _collapseDots)

def pushDownRewrites(kast):
    def _pushDownRewrites(_kast):
        if isKRewrite(_kast):
            lhs = _kast["lhs"]
            rhs = _kast["rhs"]
            if lhs == rhs:
                return lhs
            if  isKApply(lhs) and isKApply(rhs) and lhs["label"] == rhs["label"] and isCellKLabel(lhs["label"]) \
            and len(lhs["args"]) == len(rhs["args"]):
                    newArgs = [ KRewrite(lArg, rArg) for (lArg, rArg) in zip(lhs["args"], rhs["args"]) ]
                    return KApply(lhs["label"], newArgs)
            if isKSequence(lhs) and isKSequence(rhs) and len(lhs['items']) > 0 and len(rhs['items']) > 0:
                if lhs['items'][0] == rhs['items'][0]:
                    lowerRewrite = KRewrite(KSequence(lhs['items'][1:]), KSequence(rhs['items'][1:]))
                    return KSequence([lhs['items'][0], lowerRewrite])
                if lhs['items'][-1] == rhs['items'][-1]:
                    lowerRewrite = KRewrite(KSequence(lhs['items'][0:-1]), KSequence(rhs['items'][0:-1]))
                    return KSequence([lowerRewrite, lhs['items'][-1]])
            if isKSequence(lhs) and len(lhs['items']) > 0 and isKVariable(lhs['items'][-1]) and isKVariable(rhs) and lhs['items'][-1] == rhs:
                return KSequence([KRewrite(KSequence(lhs['items'][0:-1]), KConstant(klabelEmptyK)), rhs])
        return _kast
    return traverseTopDown(kast, _pushDownRewrites)

def inlineCellMaps(kast):
    """Ensure that cell map collections are printed nicely, not as Maps."

    -   Input: kast term.
    -   Output: kast term with cell maps inlined.
    """
    def _inlineCellMaps(_kast):
        if isKApply(_kast) and _kast["label"] == "_|->_":
            mapKey = _kast["args"][0]
            if isKApply(mapKey) and isCellKLabel(mapKey["label"]):
                return _kast["args"][1]
        return _kast
    return traverseBottomUp(kast, _inlineCellMaps)

def removeSemanticCasts(kast):
    """Remove injected `#SemanticCast*` nodes in AST.

    -   Input: kast (possibly) containing automatically injected `#SemanticCast*` KApply nodes.
    -   Output: kast without the `#SemanticCast*` nodes.
    """
    def _removeSemanticCasts(_kast):
        if isKApply(_kast) and len(_kast['args']) == 1 and _kast['label'].startswith('#SemanticCast'):
            return _kast['args'][0]
        return _kast
    return traverseBottomUp(kast, _removeSemanticCasts)

def uselessVarsToDots(kast, requires = None, ensures = None):
    """Structurally abstract away useless variables.

    -   Input: kast term, and a requires clause and ensures clause.
    -   Output: kast term with the useless vars structurally abstracted.
    """

    numOccurances = {}
    def _getNumOccurances(_kast):
        if isKVariable(_kast):
            vName = _kast["name"]
            if vName in numOccurances:
                numOccurances[vName] += 1
            else:
                numOccurances[vName] = 1

    collectBottomUp(kast, _getNumOccurances)
    if requires is not None:
        collectBottomUp(requires, _getNumOccurances)
    if ensures is not None:
        collectBottomUp(ensures, _getNumOccurances)

    def _collapseUselessVars(_kast):
        if isKApply(_kast) and isCellKLabel(_kast["label"]):
            newArgs = []
            for arg in _kast["args"]:
                if isKVariable(arg) and numOccurances[arg["name"]] == 1:
                    newArgs.append(ktokenDots)
                else:
                    newArgs.append(arg)
            return KApply(_kast["label"], newArgs)
        return _kast

    return traverseBottomUp(kast, _collapseUselessVars)

def onAttributes(kast, effect):
    if isKAs(kast):
        return KAs(kast['pattern'], kast['alias'], att = effect(kast['att']))
    elif isKRule(kast):
        return KRule(kast['body'], requires = kast['requires'], ensures = kast['ensures'], att = effect(kast['att']))
    elif isKClaim(kast):
        return KClaim(kast['body'], requires = kast['requires'], ensures = kast['ensures'], att = effect(kast['att']))
    elif isKContext(kast):
        return KContext(kast['body'], requires = kast['requires'], att = effect(kast['att']))
    elif isKBubble(kast):
        return KBubble(kast['sentenceType'], kast['contents'], att = effect(kast['att']))
    elif isKProduction(kast):
        return KProduction(kast['productionItems'], kast['sort'], att = effect(kast['att']))
    elif isKSyntaxAssociativity(kast):
        return KSyntaxAssociativity(kast['assoc'], tags = kast['tags'], att = effect(kast['att']))
    elif isKSyntaxPriority(kast):
        return KSyntaxPriority(priorities = kast['priorities'], att = effect(kast['att']))
    elif isKSyntaxSort(kast):
        return KSyntaxSort(kast['sort'], att = effect(kast['att']))
    elif isKSortSynonym(kast):
        return KSortSynonym(kast['newSort'], kast['oldSort'], att = effect(kast['att']))
    elif isKSyntaxLexical(kast):
        return KSyntaxLexical(kast['name'], kast['regex'], att = effect(kast['att']))
    elif isKFlatModule(kast):
        localSentences = [ onAttributes(sent, effect) for sent in kast['localSentences'] ]
        return KFlatModule(kast['name'], kast['imports'], localSentences, att = effect(kast['att']))
    elif isKDefinition(kast):
        modules = [ onAttributes(mod, effect) for mod in kast['modules'] ]
        requires = None if 'requires' not in kast else kast['requires']
        return KDefinition(kast['mainModule'], modules, requires = requires, att = effect(kast['att']))
    _fatal('No attributes for: ' + kast['node'] + '.')

def minimizeTerm(term, requires = None, ensures = None):
    """Minimize a K term for pretty-printing.

    -   Input: kast term, and optionally requires and ensures clauses with constraints.
    -   Output: kast term minimized.
        -   Variables only used once will be removed.
        -   Unused cells will be abstracted.
        -   Attempt to remove useless conditions.
    """
    term = inlineCellMaps(term)
    term = removeSemanticCasts(term)
    term = uselessVarsToDots(term, requires = requires, ensures = ensures)
    term = collapseDots(term)
    return term

def minimizeRule(rule):
    """Minimize a K rule or claim for pretty-printing.

    -   Input: kast representing a K rule or claim.
    -   Output: kast with the rule or claim minimized:
        -   Variables only used once will be removed.
        -   Unused cells will be abstracted.
        -   Attempt to remove useless side-conditions.
    """
    if not isKRule(rule) and not isKClaim(rule):
        return rule

    ruleBody     = rule["body"]
    ruleRequires = rule["requires"]
    ruleEnsures  = rule["ensures"]
    ruleAtts     = rule["att"]

    if ruleRequires is not None:
        constraints = flattenLabel("_andBool_", ruleRequires)
        ruleRequires = KToken("true", "Bool")
        substitutions = {}
        for constraint in constraints:
            if isKApply(constraint) and constraint["label"] == "_==K_":
                lhs = constraint["args"][0]
                rhs = constraint["args"][1]
                if isKVariable(lhs):
                    substitutions[lhs["name"]] = rhs
                    continue
                if isKApply(lhs) and lhs["label"] == "Map:lookup":
                    mapName  = lhs["args"][0]["name"]
                    mapEntry = KApply("_|->_", [lhs["args"][1], rhs])
                    substitutions[mapName] = KApply("_Map_", [mapEntry, KVariable(mapName + "_REST")])
                    continue
            ruleRequires = KApply("_andBool_", [ruleRequires, constraint])

        ruleBody = substitute(ruleBody, substitutions)

        ruleRequires = simplifyBool(unsafeMlPredToBool(ruleRequires))
        ruleEnsures  = simplifyBool(unsafeMlPredToBool(ruleEnsures))

        ruleRequires = None if ruleRequires == KToken('true', 'Bool') else ruleRequires
        ruleEnsures  = None if ruleEnsures  == KToken('true', 'Bool') else ruleEnsures

    ruleBody = minimizeTerm(ruleBody, requires = ruleRequires, ensures = ruleEnsures)

    if ruleRequires == KToken("true", "Bool"):
        ruleRequires = None
    if isKRule(rule):
        return KRule(ruleBody, requires = ruleRequires, ensures = ruleEnsures, att = ruleAtts)
    else:
        return KClaim(ruleBody, requires = ruleRequires, ensures = ruleEnsures, att = ruleAtts)

def pushDownRewritesRule(rule):
    if not isKRule(rule):
        return rule

    newRuleBody = pushDownRewrites(rule['body'])
    return KRule(newRuleBody, requires = rule['requires'], ensures = rule['ensures'], att = rule['att'])

def removeSourceMap(k):
    """Remove source map information from a given definition.

    Input: A JSON encoded K object.
    Output: The same JSON encoded object, with all source information stripped.
    """
    def _removeSourceMap(att):
        if isKAtt(att):
            atts = att['att']
            newAtts = { }
            for attKey in atts.keys():
                if attKey != 'org.kframework.attributes.Source' and attKey != 'org.kframework.attributes.Location':
                    newAtts[attKey] = atts[attKey]
            return KAtt(atts = newAtts)
    return onAttributes(k, _removeSourceMap)

def readKastTerm(termPath):
    with open(termPath, "r") as termFile:
        return json.loads(termFile.read())['term']

def writeKDefinition(fileName, kDef, symbolTable):
    if not isKDefinition(kDef):
        _notif("Not a K Definition!")
        print(kDef)
        sys.exit(1)
    specText = prettyPrintKast(kDef, symbolTable)
    with open(fileName, "w") as sfile:
        sfile.write(specText)
        _notif("Wrote spec file: " + fileName)
        print(specText)
        sys.stdout.flush()
        return
    _fatal("Could not write spec file: " + fileName)
