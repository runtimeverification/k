import sys
from pathlib import Path
from typing import Callable, Dict

from ..kast import (
    KApply,
    KAs,
    KAst,
    KAtt,
    KBubble,
    KClaim,
    KContext,
    KDefinition,
    KFlatModule,
    KImport,
    KNonTerminal,
    KProduction,
    KRegexTerminal,
    KRequire,
    KRewrite,
    KRule,
    KSequence,
    KSort,
    KSortSynonym,
    KSyntaxAssociativity,
    KSyntaxLexical,
    KSyntaxPriority,
    KSyntaxSort,
    KTerminal,
    KToken,
    KVariable,
    flattenLabel,
    ktokenDots,
    readKastTerm,
)
from ..prelude import Bool, Labels
from ..utils import hash_str

SymbolTable = Dict[str, Callable]


class KPrint:
    """Given a kompiled directory, build an unparser for it.
    """

    def __init__(self, kompiled_directory: str):
        self.kompiled_directory = Path(kompiled_directory)
        self.definition = readKastTerm(self.kompiled_directory / 'compiled.json')
        self.symbol_table = build_symbol_table(self.definition, opinionated=True)
        self.definition_hash = hash_str(self.definition)

    def pretty_print(self, kast: KAst, debug=False):
        """Given a KAST term, pretty-print it using the current definition.

        -   Input: KAST term in JSON.
        -   Output: Best-effort pretty-printed representation of the KAST term.
        """
        return prettyPrintKast(kast, self.symbol_table, debug=debug)


def unparser_for_production(prod):

    def _unparser(*args):
        index = 0
        result = []
        for item in prod.items:
            if type(item) is KTerminal:
                result.append(item.value)
            elif type(item) is KNonTerminal and index < len(args):
                result.append(args[index])
                index += 1
        return ' '.join(result)

    return _unparser


def build_symbol_table(definition: KDefinition, opinionated=False) -> SymbolTable:
    """Build the unparsing symbol table given a JSON encoded definition.

    -   Input: JSON encoded K definition.
    -   Return: Python dictionary mapping klabels to automatically generated unparsers.
    """
    symbol_table = {}
    for module in definition.modules:
        for prod in module.syntax_productions:
            assert(prod.klabel)
            label = prod.klabel.name
            if 'symbol' in prod.att and 'klabel' in prod.att:
                label = prod.att['klabel']
            unparser = unparser_for_production(prod)
            symbol_table[label] = unparser

    if opinionated:
        symbol_table['#And'] = lambda c1, c2: c1 + '\n#And ' + c2
        symbol_table['#Or'] = lambda c1, c2: c1 + '\n#Or\n' + indent(c2, size=4)

    return symbol_table


def prettyPrintKast(kast: KAst, symbol_table: SymbolTable, debug=False):
    """Print out KAST terms/outer syntax.

    -   Input: KAST term.
    -   Output: Best-effort string representation of KAST term.
    """
    if debug:
        sys.stderr.write(str(kast))
        sys.stderr.write('\n')
        sys.stderr.flush()
    if type(kast) is KVariable:
        return kast.name
    if type(kast) is KSort:
        return kast.name
    if type(kast) is KToken:
        return kast.token
    if type(kast) is KApply:
        label = kast.label.name
        args = kast.args
        unparsedArgs = [prettyPrintKast(arg, symbol_table, debug=debug) for arg in args]
        if kast.is_cell:
            cellContents = '\n'.join(unparsedArgs).rstrip()
            cellStr = label + '\n' + indent(cellContents) + '\n</' + label[1:]
            return cellStr.rstrip()
        unparser = appliedLabelStr(label) if label not in symbol_table else symbol_table[label]
        return unparser(*unparsedArgs)
    if type(kast) is KAs:
        patternStr = prettyPrintKast(kast.pattern, symbol_table, debug=debug)
        aliasStr = prettyPrintKast(kast.alias, symbol_table, debug=debug)
        return patternStr + ' #as ' + aliasStr
    if type(kast) is KRewrite:
        lhsStr = prettyPrintKast(kast.lhs, symbol_table, debug=debug)
        rhsStr = prettyPrintKast(kast.rhs, symbol_table, debug=debug)
        return '( ' + lhsStr + ' => ' + rhsStr + ' )'
    if type(kast) is KSequence:
        if kast.arity == 0:
            return prettyPrintKast(KApply(Labels.EMPTY_K), symbol_table, debug=debug)
        if kast.arity == 1:
            return prettyPrintKast(kast.items[0], symbol_table, debug=debug)
        unparsedKSequence = '\n~> '.join([prettyPrintKast(item, symbol_table, debug=debug) for item in kast.items[0:-1]])
        if kast.items[-1] == ktokenDots:
            unparsedKSequence = unparsedKSequence + '\n' + prettyPrintKast(ktokenDots, symbol_table, debug=debug)
        else:
            unparsedKSequence = unparsedKSequence + '\n~> ' + prettyPrintKast(kast.items[-1], symbol_table, debug=debug)
        return unparsedKSequence
    if type(kast) is KTerminal:
        return '"' + kast.value + '"'
    if type(kast) is KRegexTerminal:
        return 'r"' + kast.regex + '"'
    if type(kast) is KNonTerminal:
        return prettyPrintKast(kast.sort, symbol_table, debug=debug)
    if type(kast) is KProduction:
        if 'klabel' not in kast.att and kast.klabel:
            kast = kast.update_atts({'klabel': kast.klabel.name})
        sortStr = prettyPrintKast(kast.sort, symbol_table, debug=debug)
        if not kast.items:
            return 'syntax ' + sortStr
        productionStr = ' '.join([prettyPrintKast(pi, symbol_table, debug=debug) for pi in kast.items])
        attStr = prettyPrintKast(kast.att, symbol_table, debug=debug)
        return 'syntax ' + sortStr + ' ::= ' + productionStr + ' ' + attStr
    if type(kast) is KSyntaxSort:
        sortStr = prettyPrintKast(kast.sort, symbol_table, debug=debug)
        attStr = prettyPrintKast(kast.att, symbol_table, debug=debug)
        return 'syntax ' + sortStr + ' ' + attStr
    if type(kast) is KSortSynonym:
        newSortStr = prettyPrintKast(kast.new_sort, symbol_table, debug=debug)
        oldSortStr = prettyPrintKast(kast.old_sort, symbol_table, debug=debug)
        attStr = prettyPrintKast(kast.att, symbol_table, debug=debug)
        return 'syntax ' + newSortStr + ' = ' + oldSortStr + ' ' + attStr
    if type(kast) is KSyntaxLexical:
        nameStr = kast.name
        regexStr = kast.regex
        attStr = prettyPrintKast(kast.att, symbol_table, debug=debug)
        # todo: proper escaping
        return 'syntax lexical ' + nameStr + ' = r"' + regexStr + '" ' + attStr
    if type(kast) is KSyntaxAssociativity:
        assocStr = kast.assoc.value
        tagsStr = ' '.join(kast.tags)
        attStr = prettyPrintKast(kast.att, symbol_table, debug=debug)
        return 'syntax associativity ' + assocStr + ' ' + tagsStr + ' ' + attStr
    if type(kast) is KSyntaxPriority:
        prioritiesStr = ' > '.join([' '.join(group) for group in kast.priorities])
        attStr = prettyPrintKast(kast.att, symbol_table, debug=debug)
        return 'syntax priority ' + prioritiesStr + ' ' + attStr
    if type(kast) is KBubble:
        body = '// KBubble(' + kast.sentence_type + ', ' + kast.content + ')'
        attStr = prettyPrintKast(kast.att, symbol_table, debug=debug)
        return body + ' ' + attStr
    if type(kast) is KRule or type(kast) is KClaim:
        body = '\n     '.join(prettyPrintKast(kast.body, symbol_table, debug=debug).split('\n'))
        ruleStr = 'rule ' if type(kast) is KRule else 'claim '
        if 'label' in kast.att:
            ruleStr = ruleStr + '[' + kast.att['label'] + ']:'
        ruleStr = ruleStr + ' ' + body
        attsStr = prettyPrintKast(kast.att, symbol_table, debug=debug)
        if kast.requires != Bool.true:
            requiresStr = 'requires ' + '\n  '.join(prettyPrintKastBool(kast.requires, symbol_table, debug=debug).split('\n'))
            ruleStr = ruleStr + '\n  ' + requiresStr
        if kast.ensures != Bool.true:
            ensuresStr = 'ensures ' + '\n  '.join(prettyPrintKastBool(kast.ensures, symbol_table, debug=debug).split('\n'))
            ruleStr = ruleStr + '\n   ' + ensuresStr
        return ruleStr + '\n  ' + attsStr
    if type(kast) is KContext:
        body = indent(prettyPrintKast(kast.body, symbol_table, debug=debug))
        contextStr = 'context alias ' + body
        requiresStr = ''
        attsStr = prettyPrintKast(kast.att, symbol_table, debug=debug)
        if kast.requires != Bool.true:
            requiresStr = prettyPrintKast(kast.requires, symbol_table, debug=debug)
            requiresStr = 'requires ' + indent(requiresStr)
        return contextStr + '\n  ' + requiresStr + '\n  ' + attsStr
    if type(kast) is KAtt:
        if not kast.atts:
            return ''
        attStrs = [k + '(' + v + ')' for k, v in kast.atts.items()]
        return '[' + ', '.join(attStrs) + ']'
    if type(kast) is KImport:
        return ' '.join(['imports', ('public' if kast.public else 'private'), kast.name])
    if type(kast) is KFlatModule:
        name = kast.name
        imports = '\n'.join([prettyPrintKast(kimport, symbol_table, debug=debug) for kimport in kast.imports])
        sentences = '\n\n'.join([prettyPrintKast(sentence, symbol_table, debug=debug) for sentence in kast.sentences])
        contents = imports + '\n\n' + sentences
        return 'module ' + name + '\n    ' + '\n    '.join(contents.split('\n')) + '\n\nendmodule'
    if type(kast) is KRequire:
        return 'requires "' + kast.require + '"'
    if type(kast) is KDefinition:
        requires = '\n'.join([prettyPrintKast(require, symbol_table, debug=debug) for require in kast.requires])
        modules = '\n\n'.join([prettyPrintKast(module, symbol_table, debug=debug) for module in kast.modules])
        return requires + '\n\n' + modules

    raise ValueError(f'Error unparsing: {kast}')


def prettyPrintKastBool(kast, symbol_table, debug=False):
    """Print out KAST requires/ensures clause.

    -   Input: KAST Bool for requires/ensures clause.
    -   Output: Best-effort string representation of KAST term.
    """
    if debug:
        sys.stderr.write(str(kast))
        sys.stderr.write('\n')
        sys.stderr.flush()
    if type(kast) is KApply and kast.label.name in ['_andBool_', '_orBool_']:
        clauses = [prettyPrintKastBool(c, symbol_table, debug=debug) for c in flattenLabel(kast.label.name, kast)]
        head = kast.label.name.replace('_', ' ')
        if head == ' orBool ':
            head = '  orBool '
        separator = ' ' * (len(head) - 7)
        spacer = ' ' * len(head)

        def joinSep(s):
            return ('\n' + separator).join(s.split('\n'))

        clauses = ['( ' + joinSep(clauses[0])] + [head + '( ' + joinSep(c) for c in clauses[1:]] + [spacer + (')' * len(clauses))]
        return '\n'.join(clauses)
    else:
        return prettyPrintKast(kast, symbol_table, debug=debug)


def paren(printer):
    return (lambda *args: '( ' + printer(*args) + ' )')


def appliedLabelStr(symbol):
    return (lambda *args: symbol + ' ( ' + ' , '.join(args) + ' )')


def indent(input, size=2):
    return '\n'.join([(' ' * size) + line for line in input.split('\n')])
