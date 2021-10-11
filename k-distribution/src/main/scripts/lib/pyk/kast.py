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
    return { 'node': 'KApply', 'label': label, 'variable': False, 'arity': len(args), 'args': args }

def isKApply(k):
    return k['node'] == 'KApply'

def KAs(pattern, alias, att = None):
    return { 'node': 'KAs', 'pattern': pattern, 'alias': alias, 'att': att }

def isKAs(k):
    return k['node'] == 'KAs'

def KConstant(label):
    return KApply(label, [])

def isKConstant(k):
    return isKApply(k) and len(k['args']) == 0

def KSequence(items):
    return { 'node': 'KSequence', 'arity': len(items), 'items': items }

def isKSequence(k):
    return k['node'] == 'KSequence'

def KVariable(name):
    return { 'node' : 'KVariable', 'name': name, 'originalName': name }

def isKVariable(k):
    return k['node'] == 'KVariable'

def KToken(token, sort):
    return { 'node' : 'KToken', 'sort': sort, 'token': token}

def isKToken(k):
    return k['node'] == 'KToken'

def KRewrite(lhs, rhs):
    return { 'node': 'KRewrite', 'lhs': lhs, 'rhs': rhs }

def isKRewrite(k):
    return k['node'] == 'KRewrite'

def KAtt(atts = {}):
    return {'node': 'KAtt', 'att': atts}

def isKAtt(k):
    return k['node'] == 'KAtt'

def KRule(body, requires = None, ensures = None, att = None):
    return { 'node': 'KRule', 'body': body, 'requires': requires, 'ensures': ensures, 'att': att }

def isKRule(k):
    return k['node'] == 'KRule'

def KClaim(body, requires = None, ensures = None, att = None):
    return { 'node': 'KClaim', 'body': body, 'requires': requires, 'ensures': ensures, 'att': att }

def isKClaim(k):
    return k['node'] == 'KClaim'

def KContext(body, requires = None, ensures = None, att = None):
    return { 'node': 'KContext', 'body': body, 'requires': requires, 'att': att }

def isKContext(k):
    return k['node'] == 'KContext'

def KBubble(sentenceType, contents, att = None):
    return { 'node': 'KBubble', 'sentenceType': sentenceType, 'contents': contents, 'att': att }

def isKBubble(k):
    return k['node'] == 'KBubble'

def KProduction(productionItems, sort, att = None):
    return { 'node': 'KProduction', 'productionItems': productionItems, 'sort': sort, 'att': att }

def isKProduction(k):
    return k['node'] == 'KProduction'

def KNonTerminal(sort):
    return { 'node': 'KNonTerminal', 'sort': sort }

def isKNonTerminal(k):
    return k['node'] == 'KNonTerminal'

def KTerminal(value):
    return { 'node': 'KTerminal', 'value': value}

def isKTerminal(k):
    return k['node'] == 'KTerminal'

def KRegexTerminal(regex, precedeRegex = None, followRegex = None):
    return { 'node': 'KRegexTerminal', 'regex': regex, 'precedeRegex': precedeRegex, 'followRegex': followRegex }

def isKRegexTerminal(k):
    return k['node'] == 'KRegexTerminal'

def KSort(name):
    return { 'node': 'KSort', 'name': name }

def isKSort(k):
    return k['node'] == 'KSort'

def KSyntaxAssociativity(assoc, tags = [], att = None):
    return { 'node': 'KSyntaxAssociativity', 'assoc': assoc, 'tags': tags, 'att': att }

def isKSyntaxAssociativity(k):
    return k['node'] == 'KSyntaxAssociativity'

def KSyntaxPriority(priorities = [], att = None):
    return { 'node': 'KSyntaxPriority', 'priorities': priorities, 'att': att }

def isKSyntaxPriority(k):
    return k['node'] == 'KSyntaxPriority'

def KSyntaxSort(sort, att = None):
    return { 'node': 'KSyntaxSort', 'sort': sort, 'att': att }

def isKSyntaxSort(k):
    return k['node'] == 'KSyntaxSort'

def KSortSynonym(newSort, oldSort, att = None):
    return { 'node': 'KSortSynonym', 'newSort': newSort, 'oldSort': oldSort, 'att': att }

def isKSortSynonym(k):
    return k['node'] == 'KSortSynonym'

def KSyntaxLexical(newSort, oldSort, att = None):
    return { 'node': 'KSyntaxLexical', 'newSort': newSort, 'oldSort': oldSort, 'att': att }

def isKSyntaxLexical(k):
    return k['node'] == 'KSyntaxLexical'

def KFlatModule(name, imports, localSentences, att = None):
    return { 'node': 'KFlatModule', 'name': name, 'imports': imports, 'localSentences': localSentences, 'att': att }

def isKFlatModule(k):
    return k['node'] == 'KFlatModule'

def KRequire(krequire):
    return { 'node': 'KRequire', 'require': krequire }

def isKRequire(k):
    return k['node'] == 'KRequire'

def KDefinition(mainModule, modules, requires = None, att = None):
    return { 'node': 'KDefinition', 'mainModule': mainModule, 'modules': modules, 'requires': requires, 'att': att }

def isKDefinition(k):
    return k['node'] == 'KDefinition'

def isCellKLabel(label):
    return len(label) > 1 and label[0] == '<' and label[-1] == '>'

def getAttribute(k, key):
    """Returns the value of the attribute if present, None otherwise.

    -   Input: Kast with a KAtt, and attribute name.
    -   Output: Attribute value if present, otherwise None.
    """
    if 'att' in k and k['att'] is not None and isKAtt(k['att']):
        katts = k['att']['att']
        if key in katts.keys():
            return katts[key]
    return None

def addAttributes(kast, att):
    """Returns the input Kast with the given attributes added.

    -   Input: Kast term, and attribute dictionary.
    -   Output: Same Kast term, with the attributes overwritten/added.
    """
    if isKAtt(kast):
        return KAtt(combineDicts(att, kast['att']))
    if isKRule(kast):
        return KRule(kast['body'], requires = kast['requires'], ensures = kast['ensures'], att = addAttributes(kast['att'], att))
    if isKClaim(kast):
        return KClaim(kast['body'], requires = kast['requires'], ensures = kast['ensures'], att = addAttributes(kast['att'], att))
    if isKProduction(kast):
        return KProduction(kast['productionItems'], kast['sort'], att = addAttributes(kast['att'], att))
    else:
        _notif('Do not know how to add attributes to KAST!')
        sys.stderr.write(str(kast))
        sys.stderr.flush()
        sys.exit(1)

klabelCells   = '#KCells'
klabelEmptyK  = '#EmptyK'

ktokenDots = KToken('...', 'K')

def paren(printer):
    return (lambda *args: '( ' + printer(*args) + ' )')

def binOpStr(symbol):
    return (lambda a1, a2: a1 + ' ' + symbol + ' ' + a2)

def appliedLabelStr(symbol):
    return (lambda *args: symbol + ' ( ' + ' , '.join(args) + ' )')

def constLabel(symbol):
    return (lambda: symbol)

def assocWithUnit(assocJoin, unit):
    def _assocWithUnit(*args):
        newArgs = [ arg for arg in args if arg != unit ]
        return assocJoin.join(newArgs)
    return _assocWithUnit

def underbarUnparsing(symbol):
    splitSymbol = symbol.split('_')
    numArgs = len([symb for symb in splitSymbol if symb == ''])
    def _underbarUnparsing(*args):
        result = []
        i = 0
        for symb in splitSymbol:
            if symb != '':
                result.append(symb)
            if i < len(args):
                result.append(args[i])
                i += 1
        return ' '.join(result)
    return _underbarUnparsing

def indent(input, size = 2):
    return '\n'.join([(' ' * size) + l for l in input.split('\n')])

def newLines(input):
    return '\n'.join(input)

def buildSymbolTable(definition, opinionated = False):
    """Build the unparsing symbol table given a JSON encoded definition.

    -   Input: JSON encoded K definition.
    -   Return: Python dictionary mapping klabels to automatically generated unparsers.
    """
    if not isKDefinition(definition):
        _fatal('Must supply a KDefinition!')

    def _unparserFromProductionItems(prodItems):
        unparseString = ''
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

    if opinionated:
        symbolTable [ '#And' ] = lambda c1, c2: c1 + '\n#And ' + c2
        symbolTable [ '#Or'  ] = lambda c1, c2: c1 + '\n#Or\n'  + indent(c2, size = 4)

    return symbolTable

def prettyPrintKast(kast, symbolTable, debug = False):
    """Print out KAST terms/outer syntax.

    -   Input: KAST term.
    -   Output: Best-effort string representation of KAST term.
    """
    if debug:
        sys.stderr.write(str(kast))
        sys.stderr.write('\n')
        sys.stderr.flush()
    if kast is None or kast == {}:
        return ""
    if isKVariable(kast):
        return kast['originalName'] if 'originalName' in kast else kast['name']
    if isKToken(kast):
        return kast['token']
    if isKApply(kast):
        label = kast['label']
        args  = kast['args']
        unparsedArgs = [ prettyPrintKast(arg, symbolTable, debug = debug) for arg in args ]
        if isCellKLabel(label):
            cellContents = '\n'.join(unparsedArgs).rstrip()
            cellStr   = label + '\n' + indent(cellContents) + '\n</' + label[1:]
            return cellStr.rstrip()
        unparser = appliedLabelStr(label) if label not in symbolTable else symbolTable[label]
        return unparser(*unparsedArgs)
    if isKAs(kast):
        patternStr = prettyPrintKast(kast['pattern'], symbolTable, debug = debug)
        aliasStr   = prettyPrintKast(kast['alias'], symbolTable, debug = debug)
        return patternStr + ' #as ' + aliasStr
    if isKRewrite(kast):
        lhsStr = prettyPrintKast(kast['lhs'], symbolTable, debug = debug)
        rhsStr = prettyPrintKast(kast['rhs'], symbolTable, debug = debug)
        return '( ' + lhsStr + ' => ' + rhsStr + ' )'
    if isKSequence(kast):
        if len(kast['items']) == 0:
            return prettyPrintKast(KConstant(klabelEmptyK), symbolTable, debug = debug)
        if len(kast['items']) == 1:
            return prettyPrintKast(kast['items'][0], symbolTable, debug = debug)
        unparsedKSequence = '\n~> '.join([ prettyPrintKast(item, symbolTable, debug = debug) for item in kast['items'][0:-1] ])
        if kast['items'][-1] == ktokenDots:
            unparsedKSequence = unparsedKSequence + '\n' + prettyPrintKast(ktokenDots, symbolTable, debug = debug)
        else:
            unparsedKSequence = unparsedKSequence + '\n~> ' + prettyPrintKast(kast['items'][-1], symbolTable, debug = debug)
        return unparsedKSequence
    if isKSort(kast):
        return kast['name']
    if isKTerminal(kast):
        return '"' + kast['value'] + '"'
    if isKRegexTerminal(kast):
        return 'r"' + kast['regex'] + '"'
    if isKNonTerminal(kast):
        return prettyPrintKast(kast['sort'], symbolTable, debug = debug)
    if isKProduction(kast):
        if getAttribute(kast, 'klabel') is None and 'klabel' in kast:
            kast = addAttributes(kast, {'klabel' : kast['klabel']})
        sortStr       = prettyPrintKast(kast['sort'], symbolTable, debug = debug)
        productionStr = ' '.join([ prettyPrintKast(pi, symbolTable, debug = debug) for pi in kast['productionItems'] ])
        attStr        = prettyPrintKast(kast['att'], symbolTable, debug = debug)
        return 'syntax ' + sortStr + ' ::= ' + productionStr + ' ' + attStr
    if isKSyntaxSort(kast):
        sortStr = prettyPrintKast(kast['sort'], symbolTable, debug = debug)
        attStr  = prettyPrintKast(kast['att'], symbolTable, debug = debug)
        return 'syntax ' + sortStr + ' ' + attStr
    if isKSortSynonym(kast):
        newSortStr = prettyPrintKast(kast['newSort'], symbolTable, debug = debug)
        oldSortStr = prettyPrintKast(kast['oldSort'], symbolTable, debug = debug)
        attStr     = prettyPrintKast(kast['att'], symbolTable, debug = debug)
        return 'syntax ' + newSortStr + ' = ' + oldSortStr + ' ' + attStr
    if isKSyntaxLexical(kast):
        nameStr = kast['name']
        regexStr = kast['regex']
        attStr     = prettyPrintKast(kast['att'], symbolTable, debug = debug)
        # todo: proper escaping
        return 'syntax lexical ' + name + ' = r"' + regex + '" ' + attStr
    if isKSyntaxAssociativity(kast):
        assocStr = kast['assoc'].lower()
        tagsStr  = ' '.join(kast['tags'])
        attStr   = prettyPrintKast(kast['att'], symbolTable, debug = debug)
        return 'syntax associativity ' + assocStr + ' ' + tagsStr + ' ' + attStr
    if isKSyntaxPriority(kast):
        prioritiesStr = ' > '.join([ ' '.join(group) for group in kast['priorities'] ])
        attStr        = prettyPrintKast(kast['att'], symbolTable, debug = debug)
        return 'syntax priority ' + prioritiesStr + ' ' + attStr
    if isKBubble(kast):
        body = '// KBubble(' + kast['sentenceType'] + ', ' + kast['contents'] + ')'
        attStr    = prettyPrintKast(kast['att'], symbolTable, debug = debug)
        return body + ' ' + attStr
    if isKRule(kast) or isKClaim(kast):
        body        = '\n     '.join(prettyPrintKast(kast['body'], symbolTable, debug = debug).split('\n'))
        ruleStr     = 'rule ' if isKRule(kast) else 'claim '
        if getAttribute(kast, 'label') is not None:
            ruleStr = ruleStr + '[' + kast['label'] + ']:'
        ruleStr     = ruleStr + ' ' + body
        requiresStr = ''
        ensuresStr  = ''
        attsStr     = prettyPrintKast(kast['att'], symbolTable, debug = debug)
        reqEnsSymbolTable = { k: symbolTable[k] for k in symbolTable }
        reqEnsSymbolTable [ '_andBool_' ] = lambda b1, b2: b1 + '\nandBool ' + b2
        if kast['requires'] is not None:
            requiresStr = prettyPrintKast(kast['requires'], reqEnsSymbolTable, debug = debug)
            requiresStr = 'requires ' + '\n   '.join(requiresStr.split('\n'))
        if kast['ensures'] is not None:
            ensuresStr = prettyPrintKast(kast['ensures'], reqEnsSymbolTable, debug = debug)
            ensuresStr = 'ensures ' + '\n  '.join(ensuresStr.split('\n'))
        return ruleStr + '\n  ' + requiresStr + '\n  ' + ensuresStr + '\n  ' + attsStr
    if isKContext(kast):
        body        = indent(prettyPrintKast(kast['body'], symbolTable, debug = debug))
        contextStr  = 'context alias ' + body
        requiresStr = ''
        attsStr     = prettyPrintKast(kast['att'], symbolTable, debug = debug)
        if kast['requires'] is not None:
            requiresStr = prettyPrintKast(kast['requires'], symbolTable, debug = debug)
            requiresStr = 'requires ' + indent(requiresStr)
        return contextStr + '\n  ' + requiresStr + '\n  ' + attsStr
    if isKAtt(kast):
        if len(kast['att']) == 0:
            return ''
        attStrs = [ att + '(' + kast['att'][att] + ')' for att in kast['att'].keys() ]
        return '[' + ', '.join(attStrs) + ']'
    if isKFlatModule(kast):
        name = kast['name']
        imports = '\n'.join(['import ' + kimport for kimport in kast['imports']])
        localSentences = '\n\n'.join([prettyPrintKast(sent, symbolTable, debug = debug) for sent in kast['localSentences']])
        contents = imports + '\n\n' + localSentences
        return 'module ' + name                    + '\n    ' \
             + '\n    '.join(contents.split('\n')) + '\n' \
             + 'endmodule'
    if isKRequire(kast):
        return 'requires "' + kast['require'] + '"'
    if isKDefinition(kast):
        requires = '' if kast['requires'] is None else '\n'.join([prettyPrintKast(require, symbolTable, debug = debug) for require in kast['requires']])
        modules  = '\n\n'.join([prettyPrintKast(module, symbolTable, debug = debug) for module in kast['modules']])
        return requires + '\n\n' + modules

    print()
    _warning('Error unparsing kast!')
    print(kast)
    _fatal('Error unparsing!')

