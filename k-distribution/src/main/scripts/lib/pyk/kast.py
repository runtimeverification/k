#!/usr/bin/env python3

import sys
import json

def _notif(msg):
    sys.stderr.write('\n')
    sys.stderr.write(msg + '\n')
    sys.stderr.write(''.join(['=' for c in msg]) + '\n')
    sys.stderr.flush()

def _warning(msg):
    _notif('[WARNING] ' + msg)

def _fatal(msg, code = 1):
    _notif('[FATAL] ' + msg)
    sys.exit(code)

def combineDicts(*dicts):
    if len(dicts) == 0:
        return {}
    if len(dicts) == 1:
        return dicts[0]
    dict1 = dicts[0]
    dict2 = dicts[1]
    restDicts = dicts[2:]
    if dict1 is None or dict2 is None:
        return None
    intersecting_keys = set(dict1.keys()).intersection(set(dict2.keys()))
    for key in intersecting_keys:
        if dict1[key] != dict2[key]:
            return None
    newDict = { key : dict1[key] for key in dict1 }
    for key in dict2.keys():
        newDict[key] = dict2[key]
    return combineDicts(newDict, *restDicts)

def KApply(label, args):
    return { "node": "KApply", "label": label, "variable": False, "arity": len(args), "args": args }

def isKApply(k):
    return k["node"] == "KApply"

def KConstant(label):
    return KApply(label, [])

def isKConstant(k):
    return isKApply(k) and len(k['args']) == 0

def KSequence(items):
    return { "node": "KSequence", "arity": len(items), "items": items }

def isKSequence(k):
    return k["node"] == "KSequence"

def KVariable(name):
    return { "node" : "KVariable", "name": name, "originalName": name }

def isKVariable(k):
    return k["node"] == "KVariable"

def KToken(token, sort):
    return { "node" : "KToken", "sort": sort, "token": token}

def isKToken(k):
    return k["node"] == "KToken"

def KAtt(key, value):
    return {"node": "KAtt", "key": key, "value": value}

def isKAtt(k):
    return k["node"] == "KAtt"

def KRule(rule, requires = None, ensures = None, atts = None):
    return { "node": "KRule", "rule": rule, "requires": requires, "ensures": ensures, "atts": atts }

def isKRule(k):
    return k["node"] == "KRule"

def KImport(kimport):
    return { "node": "KImport", "import": kimport }

def isKImport(k):
    return k["node"] == "KImport"

def KFlatModule(name, imports, localSentences, atts = None):
    return { "node": "KFlatModule", "name": name, "imports": imports, "localSentences": localSentences, "atts": atts }

def isKFlatModule(k):
    return k["node"] == "KFlatModule"

def KRequire(krequire):
    return { "node": "KRequire", "require": krequire }

def isKRequire(k):
    return k["node"] == "KRequire"

def KDefinition(mainModule, modules, requires = None, atts = None):
    return { "node": "KDefinition", "mainModule": mainModule, "modules": modules, "requires": requires, "atts": atts }

def isKDefinition(k):
    return k["node"] == "KDefinition"

def isCellKLabel(label):
    return len(label) > 1 and label[0] == "<" and label[-1] == ">"

def addAttributes(kast, atts):
    if isKRule(kast):
        newAtts = []
        if kast["atts"] is None:
            newAtts = atts
        else:
            newAtts.extend(kast["atts"])
        return KRule(kast["rule"], requires = kast["requires"], ensures = kast["ensures"], atts = newAtts)
    else:
        notif("Don't know how to add attributes to KAST!")
        print(kast)
        sys.exit(1)

klabelRewrite = "#KRewrite"
klabelCells   = "#KCells"
klabelEmptyK  = "#EmptyK"

ktokenDots = KToken("...", "K")

def paren(printer):
    return (lambda *args: "( " + printer(*args) + " )")

def binOpStr(symbol):
    return (lambda a1, a2: a1 + " " + symbol + " " + a2)

def appliedLabelStr(symbol):
    return (lambda *args: symbol + " ( " + " , ".join(args) + " )")

def constLabel(symbol):
    return (lambda: symbol)

def assocWithUnit(assocJoin, unit):
    def _assocWithUnit(*args):
        newArgs = [ arg for arg in args if arg != unit ]
        return assocJoin.join(newArgs)
    return _assocWithUnit

def underbarUnparsing(symbol):
    splitSymbol = symbol.split("_")
    numArgs = len([symb for symb in splitSymbol if symb == ""])
    def _underbarUnparsing(*args):
        result = []
        i = 0
        for symb in splitSymbol:
            if symb != "":
                result.append(symb)
            if i < len(args):
                result.append(args[i])
                i += 1
        return " ".join(result)
    return _underbarUnparsing

def indent(input):
    return "\n".join(["  " + l for l in input.split("\n")])

# Build the symbol table of a given definition
def buildSymbolTable(definition):
    if not isKDefinition(definition):
        _fatal('Must supply a KDefinition!')

    def _unparserFromProductionItems(prodItems):
        unparseString = ""
        for prodItem in prodItems:
            if isKTerminal(prodItem):
                unparseString += prodItem['value']
            elif isKNonTerminal(prodItem):
                unparseString += '_'
        return underbarUnparsing(unparseString)

    symbolTable = { }
    for module in definition['modules']:
        for sent in module['localSentences']:
            if isKProduction(sent) and 'klabel' in sent:
                label = sent['klabel']
                if 'symbol' in sent['att']['att'] and 'klabel' in sent['att']['att']:
                    label = sent['att']['att']['klabel']
                unparser = _unparserFromProductionItems(sent['productionItems'])
                symbolTable[label] = unparser

    return symbolTable

def prettyPrintKast(kast, symbolTable):
    if kast is None or kast == {}:
        return ""
    if isKVariable(kast):
        return kast["name"]
    if isKToken(kast):
        return kast["token"]
    if isKApply(kast):
        label = kast["label"]
        args  = kast["args"]
        unparsedArgs = [ prettyPrintKast(arg, symbolTable) for arg in args ]
        if isCellKLabel(label):
            cellContents = "\n".join(unparsedArgs).rstrip()
            cellStr   = label + "\n" + indent(cellContents) + "\n</" + label[1:]
            return cellStr.rstrip()
        unparser = appliedLabelStr(label) if label not in symbolTable else symbolTable[label]
        return unparser(*unparsedArgs)
    if isKSequence(kast):
        unparsedItems = [ prettyPrintKast(item, symbolTable) for item in kast['items'] ]
        unparsedKSequence = "\n~> ".join(unparsedItems)
        if len(unparsedItems) > 1:
            unparsedKSequence = "    " + unparsedKSequence
        return unparsedKSequence
    if isKRule(kast):
        body     = "\n     ".join(prettyPrintKast(kast["rule"], symbolTable).split("\n"))
        ruleStr = "rule " + body
        requiresStr = ""
        ensuresStr  = ""
        attsStr     = ""
        if kast["requires"] is not None:
            requiresStr = prettyPrintKast(kast["requires"], symbolTable)
            requiresStr = "\n  requires " + "\n   ".join(requiresStr.split("\n"))
        if kast["ensures"] is not None:
            ensuresStr = prettyPrintKast(kast["ensures"], symbolTable)
            ensuresStr = "\n  ensures " + "\n  ".join(ensuresStr.split("\n"))
        if kast["atts"] is not None:
            attsStr = ", ".join([prettyPrintKast(att, symbolTable) for att in kast["atts"]])
            attsStr = "\n  [" + attsStr + "]"
        return ruleStr + requiresStr + ensuresStr + attsStr
    if isKAtt(kast):
        if len(kast['att']) == 0:
            return ''
        attStr = ''
        for att in kast['att'].keys():
            attStr += att + '(' + kast['att'][att] + ')'
        return '[' + attStr + ']'
    if isKImport(kast):
        return "imports " + kast["import"]
    if isKFlatModule(kast):
        name = kast["name"]
        imports = "\n".join([prettyPrintKast(kimport, symbolTable) for kimport in kast["imports"]])
        localSentences = "\n\n".join([prettyPrintKast(sent, symbolTable) for sent in kast["localSentences"]])
        contents = imports + "\n\n" + localSentences
        return "module " + name                    + "\n    " \
             + "\n    ".join(contents.split("\n")) + "\n" \
             + "endmodule"
    if isKRequire(kast):
        return "requires \"" + kast["require"] + ".k\""
    if isKDefinition(kast):
        requires = "" if kast["requires"] is None else "\n".join([prettyPrintKast(require, symbolTable) for require in kast["requires"]])
        modules  = "\n\n".join([prettyPrintKast(module, symbolTable) for module in kast["modules"]])
        return requires + "\n\n" + modules

    print()
    _warning("Error unparsing kast!")
    print(kast)
    _fatal("Error unparsing!")

