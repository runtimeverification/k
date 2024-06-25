from __future__ import annotations

from typing import TYPE_CHECKING

from ..utils import intersperse
from .att import Atts
from .inner import KApply, KToken, KVariable
from .outer import KNonTerminal, KRegexTerminal, KSequence, KTerminal

if TYPE_CHECKING:
    from . import KInner
    from .inner import KSort
    from .outer import KDefinition, KProduction


class Formatter:
    definition: KDefinition

    _indent: int
    _brackets: bool

    def __init__(self, definition: KDefinition, *, indent: int = 0, brackets: bool = True):
        self.definition = definition
        self._indent = indent
        self._brackets = brackets

    def __call__(self, term: KInner) -> str:
        return self.format(term)

    def format(self, term: KInner) -> str:
        if self._brackets:
            term = add_brackets(self.definition, term)
        return ''.join(self._format(term))

    def _format(self, term: KInner) -> list[str]:
        match term:
            case KToken(token, _):
                return [token]
            case KVariable(name, sort):
                sort_str = f':{sort.name}' if sort else ''
                return [f'{name}{sort_str}']
            case KSequence():
                return self._format_ksequence(term)
            case KApply():
                return self._format_kapply(term)
            case _:
                raise ValueError(f'Unsupported term: {term}')

    def _format_ksequence(self, ksequence: KSequence) -> list[str]:
        items = [self._format(item) for item in ksequence.items]  # recur
        items.append(['.K'])
        return [chunk for chunks in intersperse(items, [' ~> ']) for chunk in chunks]

    def _format_kapply(self, kapply: KApply) -> list[str]:
        production = self.definition.syntax_symbols[kapply.label.name]
        formatt = production.att.get(Atts.FORMAT, production.default_format)
        return [
            chunk
            for token in formatt.tokens
            for chunks in self._interpret_token(token, production, kapply)
            for chunk in chunks
        ]

    def _interpret_token(self, token: str, production: KProduction, kapply: KApply) -> list[str]:
        if not token[0] == '%':
            return [token]

        escape = token[1:]

        if escape[0].isdigit():
            try:
                index = int(escape)
            except ValueError as err:
                raise AssertionError(f'Incorrect format escape sequence: {token}') from err
            return self._interpret_index(index, production, kapply)

        assert len(escape) == 1

        match escape:
            case 'n':
                return ['\n', self._indent * '  ']
            case 'i':
                self._indent += 1
                return []
            case 'd':
                self._indent -= 1
                return []
            case 'c' | 'r':
                return []  # TODO add color support
            case _:
                return [escape]

    def _interpret_index(self, index: int, production: KProduction, kapply: KApply) -> list[str]:
        assert index > 0
        if index > len(production.items):
            raise ValueError(f'Format escape index out of bounds: {index}: {production}')

        item = production.items[index - 1]
        match item:
            case KTerminal(value):
                return [value]
            case KNonTerminal():
                arg_index = sum(isinstance(item, KNonTerminal) for item in production.items[: index - 1])
                if arg_index >= len(kapply.args):
                    raise ValueError('NonTerminal index out of bounds: {arg_index}: {kapply}')
                arg = kapply.args[arg_index]
                return self._format(arg)  # recur
            case KRegexTerminal():
                raise ValueError(f'Invalid format index escape to regex terminal: {index}: {production}')
            case _:
                raise AssertionError()


def add_brackets(definition: KDefinition, term: KInner) -> KInner:
    if not isinstance(term, KApply):
        return term
    prod = definition.symbols[term.label.name]

    args: list[KInner] = []

    arg_index = -1
    for index, item in enumerate(prod.items):
        if not isinstance(item, KNonTerminal):
            continue

        arg_index += 1
        arg = term.args[arg_index]
        arg = add_brackets(definition, arg)
        arg = _with_bracket(definition, term, arg, item.sort, index)
        args.append(arg)

    return term.let(args=args)


def _with_bracket(definition: KDefinition, parent: KApply, term: KInner, bracket_sort: KSort, index: int) -> KInner:
    if not _requires_bracket(definition, parent, term, index):
        return term

    bracket_prod = definition.brackets.get(bracket_sort)
    if not bracket_prod:
        return term

    bracket_label = bracket_prod.att[Atts.BRACKET_LABEL]['name']
    return KApply(bracket_label, term)


def _requires_bracket(definition: KDefinition, parent: KApply, term: KInner, index: int) -> bool:
    if isinstance(term, (KToken, KVariable, KSequence)):
        return False

    assert isinstance(term, KApply)

    if len(term.args) == 1:
        return False

    if _between_terminals(definition, parent, index):
        return False

    if _associativity_wrong(definition, parent, term, index):
        return True

    if _priority_wrong(definition, parent, term):
        return True

    return False


def _between_terminals(definition: KDefinition, parent: KApply, index: int) -> bool:
    prod = definition.symbols[parent.label.name]
    if index in [0, len(prod.items) - 1]:
        return False
    return all(isinstance(prod.items[index + offset], KTerminal) for offset in [-1, 1])


def _associativity_wrong(definition: KDefinition, parent: KApply, term: KApply, index: int) -> bool:
    """Return whether `term` can appear as the `index`-th child of `parent` according to associativity rules.

    A left (right) associative symbol cannot appear as the rightmost (leftmost) child of a symbol with equal priority.
    """
    parent_label = parent.label.name
    term_label = term.label.name
    prod = definition.symbols[parent_label]
    if index == 0 and term_label in definition.right_assocs.get(parent_label, ()):
        return True
    if index == len(prod.items) - 1 and term_label in definition.left_assocs.get(parent_label, ()):
        return True
    return False


def _priority_wrong(definition: KDefinition, parent: KApply, term: KApply) -> bool:
    """Return whether `term` can appear as a child of `parent` according to priority rules.

    A symbol with a lesser priority cannot appear as the child of a symbol with greater priority.
    """
    parent_label = parent.label.name
    term_label = term.label.name
    return term_label in definition.priorities.get(parent_label, ())
