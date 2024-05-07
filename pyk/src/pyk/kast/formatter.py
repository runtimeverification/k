from __future__ import annotations

from typing import TYPE_CHECKING

from ..utils import intersperse
from .att import Atts
from .inner import KApply, KToken, KVariable
from .outer import KNonTerminal, KRegexTerminal, KSequence, KTerminal

if TYPE_CHECKING:
    from . import KInner
    from .outer import KDefinition, KProduction


class Formatter:
    definition: KDefinition

    _indent: int

    def __init__(self, definition: KDefinition, *, indent: int = 0):
        self.definition = definition
        self._indent = indent

    def __call__(self, term: KInner) -> str:
        return self.format(term)

    def format(self, term: KInner) -> str:
        return ''.join(self._format(term))

    def _format(self, term: KInner) -> list[str]:
        match term:
            case KVariable(s, _) | KToken(s, _):
                return [s]
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
        production = self.definition.symbols[kapply.label.name]
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
