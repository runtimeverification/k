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
    and pattern["label"] == kast["label"] and pattern["arity"] == kast["arity"]:
        subst = {}
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
    return None

def collectBottomUp(kast, callback):
    if isKApply(kast):
        for arg in kast["args"]:
            collectBottomUp(arg, callback)
    callback(kast)

def traverseBottomUp(kast, effect):
    if isKApply(kast):
        newArgs = []
        for arg in kast["args"]:
            newArgs.append(traverseBottomUp(arg, effect))
        kast = KApply(kast["label"], newArgs)
    return effect(kast)

def traverseTopDown(kast, effect):
    newKast = effect(kast)
    if isKApply(newKast):
        newArgs = []
        for arg in newKast["args"]:
            newArgs.append(traverseTopDown(arg, effect))
        newKast = KApply(newKast["label"], newArgs)
    return newKast

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

def mlPredToBool(k):
    klabelMap = { "#And"    : "_andBool_"
                , "#Or"     : "_orBool_"
                , "#Not"    : "notBool_"
                , "#Equals" : '_==K_'
                }
    return replaceKLabels(k, klabelMap)

def simplifyBool(k):
    simplifyRules = [ (KApply("_==K_", [KVariable("#LHS"), KToken("true", "Bool")]),  KVariable("#LHS"))
                    , (KApply("_==K_", [KVariable("#LHS"), KToken("false", "Bool")]), KApply("notBool_", [KVariable("#LHS")]))
                    , (KApply("_andBool_", [KToken("true", "Bool"), KVariable("#REST")]), KVariable("#REST"))
                    , (KApply("_andBool_", [KVariable("#REST"), KToken("true", "Bool")]), KVariable("#REST"))
                    , (KApply("_andBool_", [KToken("false", "Bool"), KVariable("#REST")]), KToken("false", "Bool"))
                    , (KApply("_andBool_", [KVariable("#REST"), KToken("false", "Bool")]), KToken("false", "Bool"))
                    , (KApply("_orBool_", [KToken("false", "Bool"), KVariable("#REST")]), KVariable("#REST"))
                    , (KApply("_orBool_", [KVariable("#REST"), KToken("false", "Bool")]), KVariable("#REST"))
                    , (KApply("_orBool_", [KToken("true", "Bool"), KVariable("#REST")]), KToken("true", "Bool"))
                    , (KApply("_orBool_", [KVariable("#REST"), KToken("true", "Bool")]), KToken("true", "Bool"))
                    , (KApply("notBool_", [KToken("false", "Bool")]), KToken("true", "Bool"))
                    , (KApply("notBool_", [KToken("true", "Bool") ]), KToken("false", "Bool"))
                    , (KApply("#True", []), KToken("true", "Bool"))
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
    symbolic_config = traverseBottomUp(configuration, _replaceWithVar)
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
        return _kast
    return traverseTopDown(kast, _pushDownRewrites)

def inlineCellMaps(kast):
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

def minimizeRule(rule):
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
        ruleRequires = simplifyBool(mlPredToBool(ruleRequires))

    ruleBody = inlineCellMaps(ruleBody)
    ruleBody = removeSemanticCasts(ruleBody)
    ruleBody = uselessVarsToDots(ruleBody, requires = ruleRequires, ensures = ruleEnsures)
    ruleBody = collapseDots(ruleBody)

    if (ruleRequires == KToken("true", "Bool")):
        ruleRequires = None

    return KRule(ruleBody, requires = ruleRequires, ensures = ruleEnsures, att = ruleAtts)

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
