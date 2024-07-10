from __future__ import annotations

import logging
from collections.abc import Callable
from functools import cached_property
from typing import TYPE_CHECKING

from ..prelude.kbool import TRUE
from .att import Atts, KAtt
from .inner import KApply, KAs, KInner, KLabel, KRewrite, KSequence, KSort, KToken, KVariable
from .manip import flatten_label, sort_ac_collections, undo_aliases
from .outer import (
    KBubble,
    KClaim,
    KContext,
    KDefinition,
    KFlatModule,
    KImport,
    KNonTerminal,
    KOuter,
    KProduction,
    KRegexTerminal,
    KRequire,
    KRule,
    KRuleLike,
    KSortSynonym,
    KSyntaxAssociativity,
    KSyntaxLexical,
    KSyntaxPriority,
    KSyntaxSort,
    KTerminal,
)

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Any, Final, TypeVar

    from .kast import KAst

    RL = TypeVar('RL', bound='KRuleLike')

_LOGGER: Final = logging.getLogger(__name__)

SymbolTable = dict[str, Callable[..., str]]


class PrettyPrinter:
    definition: KDefinition
    _extra_unparsing_modules: Iterable[KFlatModule]
    _patch_symbol_table: Callable[[SymbolTable], None] | None
    _unalias: bool
    _sort_collections: bool

    def __init__(
        self,
        definition: KDefinition,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
        patch_symbol_table: Callable[[SymbolTable], None] | None = None,
        unalias: bool = True,
        sort_collections: bool = False,
    ):
        self.definition = definition
        self._extra_unparsing_modules = extra_unparsing_modules
        self._patch_symbol_table = patch_symbol_table
        self._unalias = unalias
        self._sort_collections = sort_collections

    @cached_property
    def symbol_table(self) -> SymbolTable:
        symb_table = build_symbol_table(
            self.definition,
            extra_modules=self._extra_unparsing_modules,
            opinionated=True,
        )
        if self._patch_symbol_table is not None:
            self._patch_symbol_table(symb_table)
        return symb_table

    def print(self, kast: KAst) -> str:
        """Print out KAST terms/outer syntax.

        Args:
            kast: KAST term to print.

        Returns:
            Best-effort string representation of KAST term.
        """
        _LOGGER.debug(f'Unparsing: {kast}')
        if type(kast) is KAtt:
            return self._print_katt(kast)
        if type(kast) is KSort:
            return self._print_ksort(kast)
        if type(kast) is KLabel:
            return self._print_klabel(kast)
        elif isinstance(kast, KOuter):
            return self._print_kouter(kast)
        elif isinstance(kast, KInner):
            if self._unalias:
                kast = undo_aliases(self.definition, kast)
            if self._sort_collections:
                kast = sort_ac_collections(kast)
            return self._print_kinner(kast)
        raise AssertionError(f'Error unparsing: {kast}')

    def _print_kouter(self, kast: KOuter) -> str:
        match kast:
            case KTerminal():
                return self._print_kterminal(kast)
            case KRegexTerminal():
                return self._print_kregexterminal(kast)
            case KNonTerminal():
                return self._print_knonterminal(kast)
            case KProduction():
                return self._print_kproduction(kast)
            case KSyntaxSort():
                return self._print_ksyntaxsort(kast)
            case KSortSynonym():
                return self._print_ksortsynonym(kast)
            case KSyntaxLexical():
                return self._print_ksyntaxlexical(kast)
            case KSyntaxAssociativity():
                return self._print_ksyntaxassociativity(kast)
            case KSyntaxPriority():
                return self._print_ksyntaxpriority(kast)
            case KBubble():
                return self._print_kbubble(kast)
            case KRule():
                return self._print_krule(kast)
            case KClaim():
                return self._print_kclaim(kast)
            case KContext():
                return self._print_kcontext(kast)
            case KImport():
                return self._print_kimport(kast)
            case KFlatModule():
                return self._print_kflatmodule(kast)
            case KRequire():
                return self._print_krequire(kast)
            case KDefinition():
                return self._print_kdefinition(kast)
            case _:
                raise AssertionError(f'Error unparsing: {kast}')

    def _print_kinner(self, kast: KInner) -> str:
        match kast:
            case KVariable():
                return self._print_kvariable(kast)
            case KToken():
                return self._print_ktoken(kast)
            case KApply():
                return self._print_kapply(kast)
            case KAs():
                return self._print_kas(kast)
            case KRewrite():
                return self._print_krewrite(kast)
            case KSequence():
                return self._print_ksequence(kast)
            case _:
                raise AssertionError(f'Error unparsing: {kast}')

    def _print_ksort(self, ksort: KSort) -> str:
        return ksort.name

    def _print_klabel(self, klabel: KLabel) -> str:
        return klabel.name

    def _print_kvariable(self, kvariable: KVariable) -> str:
        sort = kvariable.sort
        if not sort:
            return kvariable.name
        return kvariable.name + ':' + sort.name

    def _print_ktoken(self, ktoken: KToken) -> str:
        return ktoken.token

    def _print_kapply(self, kapply: KApply) -> str:
        label = kapply.label.name
        args = kapply.args
        unparsed_args = [self._print_kinner(arg) for arg in args]
        if kapply.is_cell:
            cell_contents = '\n'.join(unparsed_args).rstrip()
            cell_str = label + '\n' + indent(cell_contents) + '\n</' + label[1:]
            return cell_str.rstrip()
        unparser = self._applied_label_str(label) if label not in self.symbol_table else self.symbol_table[label]
        return unparser(*unparsed_args)

    def _print_kas(self, kas: KAs) -> str:
        pattern_str = self._print_kinner(kas.pattern)
        alias_str = self._print_kinner(kas.alias)
        return pattern_str + ' #as ' + alias_str

    def _print_krewrite(self, krewrite: KRewrite) -> str:
        lhs_str = self._print_kinner(krewrite.lhs)
        rhs_str = self._print_kinner(krewrite.rhs)
        return '( ' + lhs_str + ' => ' + rhs_str + ' )'

    def _print_ksequence(self, ksequence: KSequence) -> str:
        if ksequence.arity == 0:
            # TODO: Would be nice to say `return self._print_kinner(EMPTY_K)`
            return '.K'
        if ksequence.arity == 1:
            return self._print_kinner(ksequence.items[0]) + ' ~> .K'
        unparsed_k_seq = '\n~> '.join([self._print_kinner(item) for item in ksequence.items[0:-1]])
        if ksequence.items[-1] == KToken('...', KSort('K')):
            unparsed_k_seq = unparsed_k_seq + '\n' + self._print_kinner(KToken('...', KSort('K')))
        else:
            unparsed_k_seq = unparsed_k_seq + '\n~> ' + self._print_kinner(ksequence.items[-1])
        return unparsed_k_seq

    def _print_kterminal(self, kterminal: KTerminal) -> str:
        return '"' + kterminal.value + '"'

    def _print_kregexterminal(self, kregexterminal: KRegexTerminal) -> str:
        return 'r"' + kregexterminal.regex + '"'

    def _print_knonterminal(self, knonterminal: KNonTerminal) -> str:
        return self.print(knonterminal.sort)

    def _print_kproduction(self, kproduction: KProduction) -> str:
        syntax_str = 'syntax ' + self.print(kproduction.sort)
        if kproduction.items:
            syntax_str += ' ::= ' + ' '.join([self._print_kouter(pi) for pi in kproduction.items])
        att_str = self.print(kproduction.att)
        if att_str:
            syntax_str += ' ' + att_str
        return syntax_str

    def _print_ksyntaxsort(self, ksyntaxsort: KSyntaxSort) -> str:
        sort_str = self.print(ksyntaxsort.sort)
        att_str = self.print(ksyntaxsort.att)
        return 'syntax ' + sort_str + ' ' + att_str

    def _print_ksortsynonym(self, ksortsynonym: KSortSynonym) -> str:
        new_sort_str = self.print(ksortsynonym.new_sort)
        old_sort_str = self.print(ksortsynonym.old_sort)
        att_str = self.print(ksortsynonym.att)
        return 'syntax ' + new_sort_str + ' = ' + old_sort_str + ' ' + att_str

    def _print_ksyntaxlexical(self, ksyntaxlexical: KSyntaxLexical) -> str:
        name_str = ksyntaxlexical.name
        regex_str = ksyntaxlexical.regex
        att_str = self.print(ksyntaxlexical.att)
        # todo: proper escaping
        return 'syntax lexical ' + name_str + ' = r"' + regex_str + '" ' + att_str

    def _print_ksyntaxassociativity(self, ksyntaxassociativity: KSyntaxAssociativity) -> str:
        assoc_str = ksyntaxassociativity.assoc.value
        tags_str = ' '.join(ksyntaxassociativity.tags)
        att_str = self.print(ksyntaxassociativity.att)
        return 'syntax associativity ' + assoc_str + ' ' + tags_str + ' ' + att_str

    def _print_ksyntaxpriority(self, ksyntaxpriority: KSyntaxPriority) -> str:
        priorities_str = ' > '.join([' '.join(group) for group in ksyntaxpriority.priorities])
        att_str = self.print(ksyntaxpriority.att)
        return 'syntax priority ' + priorities_str + ' ' + att_str

    def _print_kbubble(self, kbubble: KBubble) -> str:
        body = '// KBubble(' + kbubble.sentence_type + ', ' + kbubble.contents + ')'
        att_str = self.print(kbubble.att)
        return body + ' ' + att_str

    def _print_krule(self, kterm: KRule) -> str:
        body = '\n     '.join(self.print(kterm.body).split('\n'))
        rule_str = 'rule '
        if Atts.LABEL in kterm.att:
            rule_str = rule_str + '[' + kterm.att[Atts.LABEL] + ']:'
        rule_str = rule_str + ' ' + body
        atts_str = self.print(kterm.att)
        if kterm.requires != TRUE:
            requires_str = 'requires ' + '\n  '.join(self._print_kast_bool(kterm.requires).split('\n'))
            rule_str = rule_str + '\n  ' + requires_str
        if kterm.ensures != TRUE:
            ensures_str = 'ensures ' + '\n  '.join(self._print_kast_bool(kterm.ensures).split('\n'))
            rule_str = rule_str + '\n   ' + ensures_str
        return rule_str + '\n  ' + atts_str

    def _print_kclaim(self, kterm: KClaim) -> str:
        body = '\n     '.join(self.print(kterm.body).split('\n'))
        rule_str = 'claim '
        if Atts.LABEL in kterm.att:
            rule_str = rule_str + '[' + kterm.att[Atts.LABEL] + ']:'
        rule_str = rule_str + ' ' + body
        atts_str = self.print(kterm.att)
        if kterm.requires != TRUE:
            requires_str = 'requires ' + '\n  '.join(self._print_kast_bool(kterm.requires).split('\n'))
            rule_str = rule_str + '\n  ' + requires_str
        if kterm.ensures != TRUE:
            ensures_str = 'ensures ' + '\n  '.join(self._print_kast_bool(kterm.ensures).split('\n'))
            rule_str = rule_str + '\n   ' + ensures_str
        return rule_str + '\n  ' + atts_str

    def _print_kcontext(self, kcontext: KContext) -> str:
        body = indent(self.print(kcontext.body))
        context_str = 'context alias ' + body
        requires_str = ''
        atts_str = self.print(kcontext.att)
        if kcontext.requires != TRUE:
            requires_str = self.print(kcontext.requires)
            requires_str = 'requires ' + indent(requires_str)
        return context_str + '\n  ' + requires_str + '\n  ' + atts_str

    def _print_katt(self, katt: KAtt) -> str:
        return katt.pretty

    def _print_kimport(self, kimport: KImport) -> str:
        return ' '.join(['imports', ('public' if kimport.public else 'private'), kimport.name])

    def _print_kflatmodule(self, kflatmodule: KFlatModule) -> str:
        name = kflatmodule.name
        imports = '\n'.join([self._print_kouter(kimport) for kimport in kflatmodule.imports])
        sentences = '\n\n'.join([self._print_kouter(sentence) for sentence in kflatmodule.sentences])
        contents = imports + '\n\n' + sentences
        return 'module ' + name + '\n    ' + '\n    '.join(contents.split('\n')) + '\n\nendmodule'

    def _print_krequire(self, krequire: KRequire) -> str:
        return 'requires "' + krequire.require + '"'

    def _print_kdefinition(self, kdefinition: KDefinition) -> str:
        requires = '\n'.join([self._print_kouter(require) for require in kdefinition.requires])
        modules = '\n\n'.join([self._print_kouter(module) for module in kdefinition.all_modules])
        return requires + '\n\n' + modules

    def _print_kast_bool(self, kast: KAst) -> str:
        """Print out KAST requires/ensures clause.

        Args:
            kast: KAST Bool for requires/ensures clause.

        Returns:
            Best-effort string representation of KAST term.
        """
        _LOGGER.debug(f'_print_kast_bool: {kast}')
        if type(kast) is KApply and kast.label.name in ['_andBool_', '_orBool_']:
            clauses = [self._print_kast_bool(c) for c in flatten_label(kast.label.name, kast)]
            head = kast.label.name.replace('_', ' ')
            if head == ' orBool ':
                head = '  orBool '
            separator = ' ' * (len(head) - 7)
            spacer = ' ' * len(head)

            def join_sep(s: str) -> str:
                return ('\n' + separator).join(s.split('\n'))

            clauses = (
                ['( ' + join_sep(clauses[0])]
                + [head + '( ' + join_sep(c) for c in clauses[1:]]
                + [spacer + (')' * len(clauses))]
            )
            return '\n'.join(clauses)
        else:
            return self.print(kast)

    def _applied_label_str(self, symbol: str) -> Callable[..., str]:
        return lambda *args: symbol + ' ( ' + ' , '.join(args) + ' )'


def build_symbol_table(
    definition: KDefinition,
    extra_modules: Iterable[KFlatModule] = (),
    opinionated: bool = False,
) -> SymbolTable:
    """Build the unparsing symbol table given a JSON encoded definition.

    Args:
        definition: JSON encoded K definition.

    Returns:
        Python dictionary mapping klabels to automatically generated unparsers.
    """
    symbol_table = {}
    all_modules = list(definition.all_modules) + ([] if extra_modules is None else list(extra_modules))
    for module in all_modules:
        for prod in module.syntax_productions:
            assert prod.klabel
            label = prod.klabel.name
            unparser = unparser_for_production(prod)

            symbol_table[label] = unparser
            if Atts.SYMBOL in prod.att:
                symbol_table[prod.att[Atts.SYMBOL]] = unparser

    if opinionated:
        symbol_table['#And'] = lambda c1, c2: c1 + '\n#And ' + c2
        symbol_table['#Or'] = lambda c1, c2: c1 + '\n#Or\n' + indent(c2, size=4)

    return symbol_table


def unparser_for_production(prod: KProduction) -> Callable[..., str]:
    def _unparser(*args: Any) -> str:
        index = 0
        result = []
        num_nonterm = len([item for item in prod.items if type(item) is KNonTerminal])
        num_named_nonterm = len([item for item in prod.items if type(item) is KNonTerminal and item.name != None])
        for item in prod.items:
            if type(item) is KTerminal:
                result.append(item.value)
            elif type(item) is KNonTerminal and index < len(args):
                if num_nonterm == num_named_nonterm:
                    if index == 0:
                        result.append('...')
                    result.append(f'{item.name}:')
                result.append(args[index])
                index += 1
        return ' '.join(result)

    return _unparser


def indent(text: str, size: int = 2) -> str:
    return '\n'.join([(' ' * size) + line for line in text.split('\n')])


def paren(printer: Callable[..., str]) -> Callable[..., str]:
    return lambda *args: '( ' + printer(*args) + ' )'


def assoc_with_unit(assoc_join: str, unit: str) -> Callable[..., str]:
    def _assoc_with_unit(*args: str) -> str:
        return assoc_join.join(arg for arg in args if arg != unit)

    return _assoc_with_unit
