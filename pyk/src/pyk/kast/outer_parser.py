from __future__ import annotations

from typing import TYPE_CHECKING

from ..dequote import dequote_string
from .outer_lexer import _EOF_TOKEN, TokenType, outer_lexer
from .outer_syntax import (
    EMPTY_ATT,
    Alias,
    Assoc,
    Att,
    Claim,
    Config,
    Context,
    Definition,
    Import,
    Lexical,
    Module,
    NonTerminal,
    PriorityBlock,
    Production,
    Require,
    Rule,
    Sort,
    SortDecl,
    SyntaxAssoc,
    SyntaxDecl,
    SyntaxDefn,
    SyntaxLexical,
    SyntaxPriority,
    SyntaxSynonym,
    Terminal,
    UserList,
)

if TYPE_CHECKING:
    from collections.abc import Collection, Iterable, Iterator
    from pathlib import Path
    from typing import Final

    from .outer_lexer import Token
    from .outer_syntax import ProductionItem, ProductionLike, Sentence, StringSentence, SyntaxSentence


_STRING_SENTENCE: Final = {
    TokenType.KW_ALIAS.value: Alias,
    TokenType.KW_CLAIM.value: Claim,
    TokenType.KW_CONFIG.value: Config,
    TokenType.KW_CONTEXT.value: Context,
    TokenType.KW_RULE.value: Rule,
}

_ASSOC_TOKENS: Final = (TokenType.KW_LEFT, TokenType.KW_RIGHT, TokenType.KW_NONASSOC)
_PRODUCTION_TOKENS: Final = (TokenType.ID_LOWER, TokenType.ID_UPPER, TokenType.STRING, TokenType.REGEX)
_PRODUCTION_ITEM_TOKENS: Final = (TokenType.STRING, TokenType.ID_LOWER, TokenType.ID_UPPER)
_ID_TOKENS: Final = (TokenType.ID_LOWER, TokenType.ID_UPPER)
_SIMPLE_BUBBLE_TOKENS: Final = (TokenType.KW_CLAIM, TokenType.KW_CONFIG, TokenType.KW_RULE)
_SORT_DECL_TOKENS: Final = (TokenType.LBRACE, TokenType.ID_UPPER)
_USER_LIST_IDS: Final = ('List', 'NeList')


class OuterParser:
    _lexer: Iterator[Token]
    _la: Token
    _la2: Token
    _source: Path | None

    def __init__(self, it: Iterable[str], source: Path | None = None):
        self._lexer = outer_lexer(it)
        self._la = next(self._lexer)
        self._la2 = next(self._lexer, _EOF_TOKEN)
        self._source = source

    def _consume(self) -> str:
        res = self._la.text
        self._la, self._la2 = self._la2, next(self._lexer, _EOF_TOKEN)
        return res

    def _error_location_string(self, t: Token) -> str:
        if not self._source:
            return ''
        return f'{self._source}:{t.loc.line}:{t.loc.col}: '

    def _unexpected_token(self, token: Token, expected_types: Iterable[TokenType] = ()) -> ValueError:
        location = ''
        message = f'Unexpected token: {token.type.name}'
        if self._source:
            location = f'{self._source}:{token.loc.line}:{token.loc.col}: '
        if expected_types:
            expected = ', '.join(sorted(token_type.name for token_type in expected_types))
            message = f'Expected {expected}, got: {token.type.name}'
        return ValueError(f'{location}{message}')

    def _match(self, token_type: TokenType) -> str:
        if self._la.type != token_type:
            raise self._unexpected_token(self._la, (token_type,))
        # _consume() inlined for efficiency
        res = self._la.text
        self._la, self._la2 = self._la2, next(self._lexer, _EOF_TOKEN)
        return res

    def _match_any(self, token_types: Collection[TokenType]) -> str:
        if self._la.type not in token_types:
            raise self._unexpected_token(self._la, token_types)
        # _consume() inlined for efficiency
        res = self._la.text
        self._la, self._la2 = self._la2, next(self._lexer, _EOF_TOKEN)
        return res

    def definition(self) -> Definition:
        requires: list[Require] = []
        while self._la.type is TokenType.KW_REQUIRES:
            requires.append(self.require())

        modules: list[Module] = []
        while self._la.type is TokenType.KW_MODULE:
            modules.append(self.module())

        return Definition(modules, requires)

    def require(self) -> Require:
        self._match(TokenType.KW_REQUIRES)
        path = _dequote_string(self._match(TokenType.STRING))
        return Require(path)

    def module(self) -> Module:
        begin_loc = self._la.loc

        self._match(TokenType.KW_MODULE)

        name = self._match(TokenType.MODNAME)
        att = self._maybe_att()

        imports: list[Import] = []
        while self._la.type is TokenType.KW_IMPORTS:
            imports.append(self.importt())

        sentences: list[Sentence] = []
        while self._la.type is not TokenType.KW_ENDMODULE:
            sentences.append(self.sentence())

        end_loc = self._la.loc + self._la.text
        self._consume()

        return Module(name, sentences, imports, att, source=self._source, location=(*begin_loc, *end_loc))

    def importt(self) -> Import:
        self._match(TokenType.KW_IMPORTS)

        public = True
        if self._la.type is TokenType.KW_PRIVATE:
            public = False
            self._consume()
        elif self._la.type is TokenType.KW_PUBLIC:
            self._consume()

        module_name = self._match(TokenType.MODNAME)

        return Import(module_name, public=public)

    def sentence(self) -> Sentence:
        if self._la.type is TokenType.KW_SYNTAX:
            return self.syntax_sentence()

        return self.string_sentence()

    def syntax_sentence(self) -> SyntaxSentence:
        self._match(TokenType.KW_SYNTAX)

        if self._la.type in _SORT_DECL_TOKENS:
            decl = self._sort_decl()

            if self._la.type is TokenType.EQ:
                self._consume()
                sort = self._sort()
                att = self._maybe_att()
                return SyntaxSynonym(decl, sort, att)

            if self._la.type is TokenType.DCOLONEQ:
                self._consume()
                blocks: list[PriorityBlock] = []
                blocks.append(self._priority_block())
                while self._la.type is TokenType.GT:
                    self._consume()
                    blocks.append(self._priority_block())
                return SyntaxDefn(decl, blocks)

            att = self._maybe_att()
            return SyntaxDecl(decl, att)

        if self._la.type is TokenType.KW_PRIORITY:
            self._consume()
            groups: list[list[str]] = []
            group: list[str] = []
            group.append(self._match(TokenType.KLABEL))
            while self._la.type is TokenType.KLABEL:
                group.append(self._consume())
            groups.append(group)
            while self._la.type is TokenType.GT:
                self._consume()
                group = []
                group.append(self._match(TokenType.KLABEL))
                while self._la.type is TokenType.KLABEL:
                    group.append(self._consume())
                groups.append(group)
            return SyntaxPriority(groups)

        if self._la.type in _ASSOC_TOKENS:
            assoc = Assoc(self._consume())
            klabels: list[str] = []
            klabels.append(self._match(TokenType.KLABEL))
            while self._la.type is TokenType.KLABEL:
                klabels.append(self._consume())
            return SyntaxAssoc(assoc, klabels)

        if self._la.type is TokenType.KW_LEXICAL:
            self._consume()
            name = self._match(TokenType.ID_UPPER)
            self._match(TokenType.EQ)
            regex = _dequote_regex(self._match(TokenType.REGEX))
            return SyntaxLexical(name, regex)

        raise self._unexpected_token(self._la)

    def _sort_decl(self) -> SortDecl:
        params: list[str] = []
        if self._la.type is TokenType.LBRACE:
            self._consume()
            params.append(self._match(TokenType.ID_UPPER))
            while self._la.type is TokenType.COMMA:
                self._consume()
                params.append(self._match(TokenType.ID_UPPER))
            self._match(TokenType.RBRACE)

        name = self._match(TokenType.ID_UPPER)

        args: list[str] = []
        if self._la.type is TokenType.LBRACE:
            self._consume()
            args.append(self._match(TokenType.ID_UPPER))
            while self._la.type is TokenType.COMMA:
                self._consume()
                args.append(self._match(TokenType.ID_UPPER))
            self._match(TokenType.RBRACE)

        return SortDecl(name, params, args)

    def _sort(self) -> Sort:
        name = self._match(TokenType.ID_UPPER)

        args: list[int | str] = []
        if self._la.type is TokenType.LBRACE:
            self._consume()
            if self._la.type is TokenType.NAT:
                args.append(int(self._consume()))
            else:
                args.append(self._match(TokenType.ID_UPPER))

            while self._la.type is TokenType.COMMA:
                self._consume()
                if self._la.type is TokenType.NAT:
                    args.append(int(self._consume()))
                else:
                    args.append(self._match(TokenType.ID_UPPER))

            self._match(TokenType.RBRACE)

        return Sort(name, args)

    def _priority_block(self) -> PriorityBlock:
        assoc: Assoc | None
        if self._la.type in _ASSOC_TOKENS:
            assoc = Assoc(self._consume())
            self._match(TokenType.COLON)
        else:
            assoc = None

        productions: list[ProductionLike] = []
        productions.append(self._production_like())
        while self._la.type is TokenType.VBAR:
            self._consume()
            productions.append(self._production_like())
        return PriorityBlock(productions, assoc)

    def _production_like(self) -> ProductionLike:
        if (
            self._la2.type is TokenType.LBRACE
            and self._la.type is TokenType.ID_UPPER
            and self._la.text in _USER_LIST_IDS
        ):
            non_empty = self._la.text[0] == 'N'
            self._consume()
            self._consume()
            sort = self._match(TokenType.ID_UPPER)
            self._match(TokenType.COMMA)
            sep = _dequote_string(self._match(TokenType.STRING))
            self._match(TokenType.RBRACE)
            att = self._maybe_att()
            return UserList(sort, sep, non_empty, att)

        items: list[ProductionItem] = []

        if self._la2.type is TokenType.LPAREN:
            items.append(Terminal(self._match_any(_ID_TOKENS)))
            items.append(Terminal(self._consume()))
            while self._la.type is not TokenType.RPAREN:
                items.append(self._non_terminal())
                if self._la.type is TokenType.COMMA:
                    items.append(Terminal(self._consume()))
                    continue
                break
            items.append(Terminal(self._match(TokenType.RPAREN)))

        else:
            items.append(self._production_item())
            while self._la.type in _PRODUCTION_ITEM_TOKENS:
                items.append(self._production_item())

        att = self._maybe_att()
        return Production(items, att)

    def _production_item(self) -> ProductionItem:
        if self._la.type is TokenType.STRING:
            return Terminal(_dequote_string(self._consume()))

        if self._la.type is TokenType.REGEX:
            return Lexical(_dequote_regex(self._consume()))

        return self._non_terminal()

    def _non_terminal(self) -> NonTerminal:
        name: str
        if self._la.type is TokenType.ID_LOWER or self._la2.type is TokenType.COLON:
            name = self._match_any(_ID_TOKENS)
            self._match(TokenType.COLON)
        else:
            name = ''

        sort = self._sort()
        return NonTerminal(sort, name)

    def string_sentence(self) -> StringSentence:
        cls_key = self._la.type.value

        if self._la.type is TokenType.KW_CONTEXT:
            self._consume()
            if self._la.type is TokenType.KW_ALIAS:
                cls_key = self._la.type.value
                self._consume()
        else:
            self._match_any(_SIMPLE_BUBBLE_TOKENS)

        cls = _STRING_SENTENCE[cls_key]

        label: str
        if self._la.type == TokenType.LBRACK:
            self._consume()
            label = self._match(TokenType.RULE_LABEL)
            self._match(TokenType.RBRACK)
            self._match(TokenType.COLON)
        else:
            label = ''

        bubble = self._match(TokenType.BUBBLE)
        att = self._maybe_att()
        return cls(bubble, label, att)

    def _maybe_att(self) -> Att:
        items: list[tuple[str, str]] = []

        if self._la.type is not TokenType.LBRACK:
            return EMPTY_ATT

        self._consume()

        while True:
            key = self._match(TokenType.ATTR_KEY)

            value: str
            if self._la.type == TokenType.LPAREN:
                self._consume()
                match self._la.type:
                    case TokenType.ATTR_CONTENT:
                        value = self._consume()
                    case TokenType.STRING:
                        value = _dequote_string(self._consume())
                    case _:
                        value = ''
                self._match(TokenType.RPAREN)
            else:
                value = ''

            items.append((key, value))

            if self._la.type != TokenType.COMMA:
                break
            else:
                self._consume()

        self._match(TokenType.RBRACK)

        return Att(items)


def _dequote_string(s: str) -> str:
    return dequote_string(s[1:-1])


def _dequote_regex(s: str) -> str:
    return dequote_string(s[2:-1])
