from __future__ import annotations

import re
from typing import TYPE_CHECKING

from .inner import KApply, KLabel, KSequence, KToken, KVariable
from .lexer import TokenType, lexer

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from typing import Final

    from . import KInner
    from .lexer import Token


TT = TokenType


class KAstParser:
    _it: Iterator[Token]
    _la: Token

    def __init__(self, it: Iterable[str]):
        self._it = lexer(it)
        self._la = next(self._it)

    def _consume(self) -> str:
        text = self._la.text
        self._la = next(self._it)
        return text

    def _match(self, expected: TokenType) -> str:
        if self._la.type is not expected:
            raise self._unexpected_token(self._la, [expected])
        text = self._la.text
        self._la = next(self._it)
        return text

    @staticmethod
    def _unexpected_token(token: Token, expected: Iterable[TokenType] = ()) -> ValueError:
        types = sorted(expected, key=lambda typ: typ.name)

        if not types:
            return ValueError(f'Unexpected token: {token.text!r}')

        if len(types) == 1:
            typ = types[0]
            return ValueError(f'Unexpected token: {token.text!r}. Expected: {typ.name}')

        type_str = ', '.join(typ.name for typ in types)
        return ValueError(f'Unexpected token: {token.text!r}. Expected one of: {type_str}')

    def eof(self) -> bool:
        return self._la.type is TT.EOF

    def k(self) -> KInner:
        if self._la.type is TT.DOTK:
            self._consume()
            return KSequence()

        items = [self.kitem()]
        while self._la.type is TT.KSEQ:
            self._consume()
            items.append(self.kitem())

        if len(items) > 1:
            return KSequence(items)

        return items[0]

    def kitem(self) -> KInner:
        match self._la.type:
            case TT.VARIABLE:
                name = self._consume()
                sort: str | None = None
                if self._la.type is TT.COLON:
                    self._consume()
                    sort = self._match(TT.SORT)
                return KVariable(name, sort)

            case TT.TOKEN:
                self._consume()
                self._match(TT.LPAREN)
                token = _unquote(self._match(TT.STRING))
                self._match(TT.COMMA)
                sort = _unquote(self._match(TT.STRING))
                self._match(TT.RPAREN)
                return KToken(token, sort)

            case TT.ID | TT.KLABEL:
                label = self.klabel()
                self._match(TT.LPAREN)
                args = self.klist()
                self._match(TT.RPAREN)
                return KApply(label, args)

            case _:
                raise self._unexpected_token(self._la, [TT.VARIABLE, TT.TOKEN, TT.ID, TT.KLABEL])

    def klabel(self) -> KLabel:
        match self._la.type:
            case TT.ID:
                return KLabel(self._consume())
            case TT.KLABEL:
                return KLabel(_unquote(self._consume()))
            case _:
                raise self._unexpected_token(self._la, [TT.ID, TT.KLABEL])

    def klist(self) -> list[KInner]:
        if self._la.type is TT.DOTKLIST:
            self._consume()
            return []

        res = [self.k()]
        while self._la.type is TT.COMMA:
            self._consume()
            res.append(self.k())
        return res


_UNQUOTE_PATTERN: Final = re.compile(r'\\.')


def _unquote(s: str) -> str:
    return _UNQUOTE_PATTERN.sub(lambda m: m.group(0)[1], s[1:-1])
