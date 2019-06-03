#!/usr/bin/env python3

import sys
import json
import util

def KApply(label, args):
    return { "node": "KApply", "label": label, "variable": False, "arity": len(args), "args": args }

def isKApply(k):
    return k["node"] == "KApply"

def KVariable(name):
    return { "node" : "KVariable", "name": name, "originalName": name }

def isKVariable(k):
    return k["node"] == "KVariable"

def KToken(token, sort):
    return { "node" : "KToken", "token": token, "sort": sort}

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

def KModule(name, imports, rules):
    return { "node": "KModule", "name": name, "imports": imports, "rules": rules }

def isKModule(k):
    return k["node"] == "KModule"

def isCellKLabel(label):
    return label[0] == "<" and label[-1] == ">"

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
    return (lambda *args: symbol + "( " + " , ".join(args) + " )")

def constLabel(symbol):
    return (lambda: symbol)

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

K_builtin_labels = { klabelRewrite : binOpStr("=>")
                   , klabelCells   : (lambda *args: "\n".join(args))
                   , klabelEmptyK  : (lambda : ".")
                   }

BOOL_expressions = { "_andBool__BOOL" : binOpStr("\nandBool")
                   , "_orBool__BOOL"  : paren(binOpStr("orBool"))
                   , "notBool__BOOL"  : (lambda a: "notBool " + a)
                   , "_==K_"          : binOpStr("==K")
                   }

INT_predicates = { "_<Int__INT-COMMON"  : binOpStr("<Int")
                 , "_>Int__INT-COMMON"  : binOpStr(">Int")
                 , "_<=Int__INT-COMMON" : binOpStr("<=Int")
                 , "_>=Int__INT-COMMON" : binOpStr(">=Int")
                 }

INT_expressions = { "_+Int_"              : paren(binOpStr("+Int"))
                  , "_-Int__INT-COMMON"   : paren(binOpStr("-Int"))
                  , "_*Int__INT-COMMON"   : paren(binOpStr("*Int"))
                  , "_/Int__INT-COMMON"   : paren(binOpStr("-Int"))
                  , "_modInt__INT-COMMON" : paren(binOpStr("modInt"))
                  , "_&Int__INT-COMMON"   : paren(binOpStr("&Int"))
                  , "_|Int__INT-COMMON"   : paren(binOpStr("|Int"))
                  , "_xorInt__INT-COMMON" : paren(binOpStr("xorInt"))
                  , "_>>Int__INT-COMMON"  : paren(binOpStr(">>Int"))
                  }

MAP_expressions = { "_[_<-_]_MAP" : paren(underbarUnparsing("_[_<-_]"))
                  , "Map:lookup"  : paren(underbarUnparsing("_[_]"))
                  , "_Map_"       : paren(underbarUnparsing("__"))
                  , "_|->_"       : paren(underbarUnparsing("_|->_"))
                  , "_[_<-undef]" : paren(underbarUnparsing("_[_ <- undef ]"))
                  }

LIST_expressions = { "_List_"   : (lambda a1, a2: a1 + " " + a2)
                   , "ListItem" : appliedLabelStr("ListItem")
                   }

SET_expressions = { "Set:in"  : binOpStr("in")
                  , "_Set_"   : (lambda a1, a2: a1 + " " + a2)
                  , "SetItem" : appliedLabelStr("SetItem")
                  }

K_symbols = util.combineDicts(K_builtin_labels, BOOL_expressions, INT_predicates, INT_expressions, MAP_expressions, LIST_expressions, SET_expressions)

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
        if isCellKLabel(label):
            contents = "\n".join([ prettyPrintKast(arg, symbolTable) for arg in args ])
            return label + "\n  " + "\n  ".join(contents.split("\n")) + "\n</" + label[1:]
        if label in symbolTable:
            newArgs = [prettyPrintKast(arg, symbolTable) for arg in args]
            return symbolTable[kast["label"]](*newArgs)
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
        kastStr = kast["key"]
        if kast["value"] == True:
            return kastStr
        else:
            return kastStr + "(" + str(kast["value"]) + ")"
    if isKImport(kast):
        return "imports " + kast["import"]
    if isKModule(kast):
        name = kast["name"]
        imports = "\n".join([prettyPrintKast(kimport, symbolTable) for kimport in kast["imports"]])
        rules = "\n\n".join([prettyPrintKast(rule, symbolTable) for rule in kast["rules"]])
        contents = imports + "\n\n" + rules
        return "module " + name                    + "\n    " \
             + "\n    ".join(contents.split("\n")) + "\n" \
             + "endmodule"

    print()
    warning("Error turning to kast!")
    print(kast)
    fatal("Error unparsing!")

def readKastTerm(termPath):
    with open(termPath, "r") as termFile:
        return normalizeKLabels(json.loads(termFile.read())['term'])

