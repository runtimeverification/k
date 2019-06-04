#!/usr/bin/env python3

import sys
import subprocess

from kast import *

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

def normalizeKLabels(k):
    newK = replaceKLabels(k, { "#And" : "_andBool__BOOL" , "#Or" : "_orBool__BOOL" })
    simplifyRules = [ (KApply("_==K_", [KVariable("#LHS"), KToken("true", "Bool")]),  KVariable("#LHS"))
                    , (KApply("_==K_", [KVariable("#LHS"), KToken("false", "Bool")]), KApply("notBool__BOOL", [KVariable("#LHS")]))
                    , (KApply("_andBool__BOOL", [KToken("true", "Bool"), KVariable("#REST")]), KVariable("#REST"))
                    , (KApply("_andBool__BOOL", [KVariable("#REST"), KToken("true", "Bool")]), KVariable("#REST"))
                    , (KApply("#True", []), KToken("true", "Bool"))
                    ]
    for rule in simplifyRules:
        newK = rewriteAnywhereWith(rule, newK)
    return newK

def rewriteWith(rule, pattern):
    (ruleLHS, ruleRHS) = rule
    matchingSubst = match(ruleLHS, pattern)
    if matchingSubst is not None:
        return substitute(ruleRHS, matchingSubst)
    return pattern

def rewriteAnywhereWith(rule, pattern):
    return traverseBottomUp(pattern, lambda p: rewriteWith(rule, p))

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

def collapseDots(kast):
    def _collapseDots(_kast):
        if isKApply(_kast):
            label = _kast["label"]
            args  = _kast["args"]
            if isCellKLabel(label):
                if len(args) == 1 and args[0] == ktokenDots:
                    return ktokenDots
            newArgs = [ arg for arg in args if arg != ktokenDots ]
            if isCellKLabel(label) and len(newArgs) == 0:
                return ktokenDots
            if len(newArgs) < len(args):
                newArgs.append(ktokenDots)
            return KApply(label, newArgs)
        return _kast
    return traverseBottomUp(kast, _collapseDots)

def pushDownRewrites(kast):
    def _pushDownRewrites(_kast):
        if isKApply(_kast) and _kast["label"] == klabelRewrite:
            lhs = _kast["args"][0]
            rhs = _kast["args"][1]
            if lhs == rhs:
                return lhs
            if  isKApply(lhs) and isKApply(rhs) and lhs["label"] == rhs["label"] and isCellKLabel(lhs["label"]) \
            and len(lhs["args"]) == len(rhs["args"]):
                    newArgs = [ KApply(klabelRewrite, [lArg, rArg]) for (lArg, rArg) in zip(lhs["args"], rhs["args"]) ]
                    return KApply(lhs["label"], newArgs)
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
    ruleBody     = rule["rule"]
    ruleRequires = rule["requires"]
    ruleEnsures  = rule["ensures"]
    ruleAtts     = rule["atts"]

    ruleBody = pushDownRewrites(ruleBody)

    if ruleRequires is not None:
        constraints = flattenLabel("_andBool__BOOL", ruleRequires)
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
            ruleRequires = KApply("_andBool__BOOL", [ruleRequires, constraint])

        ruleBody = substitute(ruleBody, substitutions)
        ruleRequires = normalizeKLabels(ruleRequires)

    ruleBody = inlineCellMaps(ruleBody)
    ruleBody = uselessVarsToDots(ruleBody, requires = ruleRequires, ensures = ruleEnsures)
    ruleBody = collapseDots(ruleBody)
    return KRule(ruleBody, requires = ruleRequires, ensures = ruleEnsures, atts = ruleAtts)

def readKastTerm(termPath):
    with open(termPath, "r") as termFile:
        return normalizeKLabels(json.loads(termFile.read())['term'])

def writeKDefinition(fileName, kDef, symbolTable):
    if not isKDefinition(kDef):
        notif("Not a K Definition!")
        print(kDef)
        sys.exit(1)
    specText = prettyPrintKast(kDef, symbolTable)
    with open(fileName, "w") as sfile:
        sfile.write(specText)
        notif("Wrote spec file: " + fileName)
        print(specText)
        sys.stdout.flush()
        return
    fatal("Could not write spec file: " + fileName)

def proveSpec(fileName, kproveArgs = []):
    notif("Attempting to prove spec: " + fileName)
    proveCommand = ["kprove", fileName] + kproveArgs
    print("Command: " + str(proveCommand))
    sys.stdout.flush()
    kproveProc = subprocess.run(proveCommand)
    if kproveProc.returncode == 0:
        notif("Proof success!!")
        return True
    else:
        notif("Proof failure!!")
        return False

