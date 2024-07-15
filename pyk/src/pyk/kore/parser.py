from __future__ import annotations

from typing import TYPE_CHECKING

from ..dequote import dequote_string
from .lexer import TokenType, kore_lexer
from .syntax import (
    DV,
    AliasDecl,
    And,
    App,
    Axiom,
    Bottom,
    Ceil,
    Claim,
    Definition,
    Equals,
    EVar,
    Exists,
    Floor,
    Forall,
    Iff,
    Implies,
    Import,
    In,
    LeftAssoc,
    Module,
    Mu,
    Next,
    Not,
    Nu,
    Or,
    Rewrites,
    RightAssoc,
    SortApp,
    SortDecl,
    SortVar,
    String,
    SVar,
    Symbol,
    SymbolDecl,
    Top,
)

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator
    from typing import Final, TypeVar, Union

    from .lexer import KoreToken
    from .syntax import (
        Assoc,
        BinaryConn,
        BinaryPred,
        MLFixpoint,
        MLPattern,
        MLQuant,
        MultiaryConn,
        NullaryConn,
        Pattern,
        RoundPred,
        Sentence,
        Sort,
        UnaryConn,
        VarPattern,
    )

    NC = TypeVar('NC', bound=NullaryConn)
    UC = TypeVar('UC', bound=Union[UnaryConn, Next])
    BC = TypeVar('BC', bound=Union[BinaryConn, Rewrites])
    MC = TypeVar('MC', bound=MultiaryConn)
    QF = TypeVar('QF', bound=MLQuant)
    FP = TypeVar('FP', bound=MLFixpoint)
    RP = TypeVar('RP', bound=RoundPred)
    BP = TypeVar('BP', bound=BinaryPred)
    AS = TypeVar('AS', bound=Assoc)

    T = TypeVar('T')


class KoreParser:
    _ML_SYMBOLS: Final = {
        TokenType.ML_TOP: 'top',
        TokenType.ML_BOTTOM: 'bottom',
        TokenType.ML_NOT: 'nott',
        TokenType.ML_AND: 'andd',
        TokenType.ML_OR: 'orr',
        TokenType.ML_IMPLIES: 'implies',
        TokenType.ML_IFF: 'iff',
        TokenType.ML_EXISTS: 'exists',
        TokenType.ML_FORALL: 'forall',
        TokenType.ML_MU: 'mu',
        TokenType.ML_NU: 'nu',
        TokenType.ML_CEIL: 'ceil',
        TokenType.ML_FLOOR: 'floor',
        TokenType.ML_EQUALS: 'equals',
        TokenType.ML_IN: 'inn',
        TokenType.ML_NEXT: 'next',
        TokenType.ML_REWRITES: 'rewrites',
        TokenType.ML_DV: 'dv',
        TokenType.ML_LEFT_ASSOC: 'left_assoc',
        TokenType.ML_RIGHT_ASSOC: 'right_assoc',
    }

    _SENTENCE_KWS: Final = {
        TokenType.KW_IMPORT: 'importt',
        TokenType.KW_SORT: 'sort_decl',
        TokenType.KW_HOOKED_SORT: 'hooked_sort_decl',
        TokenType.KW_SYMBOL: 'symbol_decl',
        TokenType.KW_HOOKED_SYMBOL: 'hooked_symbol_decl',
        TokenType.KW_ALIAS: 'alias_decl',
        TokenType.KW_AXIOM: 'axiom',
        TokenType.KW_CLAIM: 'claim',
    }

    _iter: Iterator[KoreToken]
    _la: KoreToken

    def __init__(self, text: str):
        self._iter = kore_lexer(text)
        self._la = next(self._iter)

    @property
    def eof(self) -> bool:
        return self._la.type == TokenType.EOF

    def _consume(self) -> str:
        text = self._la.text
        self._la = next(self._iter)
        return text

    def _match(self, token_type: TokenType) -> str:
        if self._la.type != token_type:
            raise ValueError(f'Expected {token_type.name}, found: {self._la.type.name}')

        return self._consume()

    def _delimited_list_of(
        self,
        parse: Callable[[], T],
        ldelim: TokenType,
        rdelim: TokenType,
        sep: TokenType = TokenType.COMMA,
    ) -> list[T]:
        res: list[T] = []

        self._match(ldelim)
        while self._la.type != rdelim:
            res.append(parse())
            if self._la.type != sep:
                break
            self._consume()
        self._consume()

        return res

    def id(self) -> str:
        return self._match(TokenType.ID)

    def symbol_id(self) -> str:
        if self._la.type == TokenType.SYMBOL_ID:
            return self._consume()

        return self._match(TokenType.ID)

    def set_var_id(self) -> str:
        return self._match(TokenType.SET_VAR_ID)

    def sort(self) -> Sort:
        name = self.id()

        if self._la.type == TokenType.LBRACE:
            sorts = self._sort_list()
            return SortApp(name, sorts)

        return SortVar(name)

    def _sort_list(self) -> list[Sort]:
        return self._delimited_list_of(self.sort, TokenType.LBRACE, TokenType.RBRACE)

    def sort_var(self) -> SortVar:
        name = self._match(TokenType.ID)
        return SortVar(name)

    def sort_app(self) -> SortApp:
        name = self._match(TokenType.ID)
        sorts = self._sort_list()
        return SortApp(name, sorts)

    def pattern(self) -> Pattern:
        if self._la.type == TokenType.STRING:
            return self.string()

        if self._la.type in self._ML_SYMBOLS:
            return self.ml_pattern()

        if self._la.type == TokenType.SYMBOL_ID:
            return self.app()

        if self._la.type == TokenType.SET_VAR_ID:
            return self.set_var()

        name = self._match(TokenType.ID)
        if self._la.type == TokenType.COLON:
            self._consume()
            sort = self.sort()
            return EVar(name, sort)

        sorts = self._sort_list()
        patterns = self._pattern_list()
        return App(name, sorts, patterns)

    def _pattern_list(self) -> list[Pattern]:
        return self._delimited_list_of(self.pattern, TokenType.LPAREN, TokenType.RPAREN)

    def string(self) -> String:
        value = self._match(TokenType.STRING)
        return String(dequote_string(value[1:-1]))

    def app(self) -> App:
        symbol = self.symbol_id()
        sorts = self._sort_list()
        patterns = self._pattern_list()
        return App(symbol, sorts, patterns)

    def var_pattern(self) -> VarPattern:
        if self._la.type == TokenType.SET_VAR_ID:
            return self.set_var()

        return self.elem_var()

    def set_var(self) -> SVar:
        name = self._match(TokenType.SET_VAR_ID)
        self._match(TokenType.COLON)
        sort = self.sort()
        return SVar(name, sort)

    def elem_var(self) -> EVar:
        name = self._match(TokenType.ID)
        self._match(TokenType.COLON)
        sort = self.sort()
        return EVar(name, sort)

    def ml_pattern(self) -> MLPattern:
        token_type = self._la.type
        if token_type not in self._ML_SYMBOLS:
            raise ValueError(f'Exected matching logic symbol, found: {self._la.text}')
        parse = getattr(self, self._ML_SYMBOLS[token_type])
        return parse()

    def _nullary(self, token_type: TokenType, cls: type[NC]) -> NC:
        self._match(token_type)
        self._match(TokenType.LBRACE)
        sort = self.sort()
        self._match(TokenType.RBRACE)
        self._match(TokenType.LPAREN)
        self._match(TokenType.RPAREN)
        # TODO Implement NullaryConn.create(symbol, sort) instead
        # TODO Consider MLConn.create(symbol, sort, patterns) as well
        return cls(sort)  # type: ignore

    def top(self) -> Top:
        return self._nullary(TokenType.ML_TOP, Top)

    def bottom(self) -> Bottom:
        return self._nullary(TokenType.ML_BOTTOM, Bottom)

    def _unary(self, token_type: TokenType, cls: type[UC]) -> UC:
        self._match(token_type)
        self._match(TokenType.LBRACE)
        sort = self.sort()
        self._match(TokenType.RBRACE)
        self._match(TokenType.LPAREN)
        pattern = self.pattern()
        self._match(TokenType.RPAREN)
        return cls(sort, pattern)  # type: ignore

    def nott(self) -> Not:
        return self._unary(TokenType.ML_NOT, Not)

    def _binary(self, token_type: TokenType, cls: type[BC]) -> BC:
        self._match(token_type)
        self._match(TokenType.LBRACE)
        sort = self.sort()
        self._match(TokenType.RBRACE)
        self._match(TokenType.LPAREN)
        left = self.pattern()
        self._match(TokenType.COMMA)
        right = self.pattern()
        self._match(TokenType.RPAREN)
        return cls(sort, left, right)  # type: ignore

    def implies(self) -> Implies:
        return self._binary(TokenType.ML_IMPLIES, Implies)

    def iff(self) -> Iff:
        return self._binary(TokenType.ML_IFF, Iff)

    def _multiary(self, token_type: TokenType, cls: type[MC]) -> MC:
        self._match(token_type)
        self._match(TokenType.LBRACE)
        sort = self.sort()
        self._match(TokenType.RBRACE)
        ops = self._delimited_list_of(self.pattern, TokenType.LPAREN, TokenType.RPAREN)
        return cls(sort, ops)  # type: ignore

    def andd(self) -> And:
        return self._multiary(TokenType.ML_AND, And)

    def orr(self) -> Or:
        return self._multiary(TokenType.ML_OR, Or)

    def _quantifier(self, token_type: TokenType, cls: type[QF]) -> QF:
        self._match(token_type)
        self._match(TokenType.LBRACE)
        sort = self.sort()
        self._match(TokenType.RBRACE)
        self._match(TokenType.LPAREN)
        var = self.elem_var()
        self._match(TokenType.COMMA)
        pattern = self.pattern()
        self._match(TokenType.RPAREN)
        return cls(sort, var, pattern)  # type: ignore

    def exists(self) -> Exists:
        return self._quantifier(TokenType.ML_EXISTS, Exists)

    def forall(self) -> Forall:
        return self._quantifier(TokenType.ML_FORALL, Forall)

    def _fixpoint(self, token_type: TokenType, cls: type[FP]) -> FP:
        self._match(token_type)
        self._match(TokenType.LBRACE)
        self._match(TokenType.RBRACE)
        self._match(TokenType.LPAREN)
        var = self.set_var()
        self._match(TokenType.COMMA)
        pattern = self.pattern()
        self._match(TokenType.RPAREN)
        return cls(var, pattern)  # type: ignore

    def mu(self) -> Mu:
        return self._fixpoint(TokenType.ML_MU, Mu)

    def nu(self) -> Nu:
        return self._fixpoint(TokenType.ML_NU, Nu)

    def _round_pred(self, token_type: TokenType, cls: type[RP]) -> RP:
        self._match(token_type)
        self._match(TokenType.LBRACE)
        op_sort = self.sort()
        self._match(TokenType.COMMA)
        sort = self.sort()
        self._match(TokenType.RBRACE)
        self._match(TokenType.LPAREN)
        pattern = self.pattern()
        self._match(TokenType.RPAREN)
        return cls(op_sort, sort, pattern)  # type: ignore

    def ceil(self) -> Ceil:
        return self._round_pred(TokenType.ML_CEIL, Ceil)

    def floor(self) -> Floor:
        return self._round_pred(TokenType.ML_FLOOR, Floor)

    def _binary_pred(self, token_type: TokenType, cls: type[BP]) -> BP:
        self._match(token_type)
        self._match(TokenType.LBRACE)
        left_sort = self.sort()
        self._match(TokenType.COMMA)
        right_sort = self.sort()
        self._match(TokenType.RBRACE)
        self._match(TokenType.LPAREN)
        left = self.pattern()
        self._match(TokenType.COMMA)
        right = self.pattern()
        self._match(TokenType.RPAREN)
        return cls(left_sort, right_sort, left, right)  # type: ignore

    def equals(self) -> Equals:
        return self._binary_pred(TokenType.ML_EQUALS, Equals)

    def inn(self) -> In:
        return self._binary_pred(TokenType.ML_IN, In)

    def next(self) -> Next:
        return self._unary(TokenType.ML_NEXT, Next)

    def rewrites(self) -> Rewrites:
        return self._binary(TokenType.ML_REWRITES, Rewrites)

    def dv(self) -> DV:
        self._match(TokenType.ML_DV)
        self._match(TokenType.LBRACE)
        sort = self.sort()
        self._match(TokenType.RBRACE)
        self._match(TokenType.LPAREN)
        value = self.string()
        self._match(TokenType.RPAREN)
        return DV(sort, value)

    def _assoc(self, token_type: TokenType, cls: type[AS]) -> AS:
        self._match(token_type)
        self._match(TokenType.LBRACE)
        self._match(TokenType.RBRACE)
        self._match(TokenType.LPAREN)
        app = self.app()
        self._match(TokenType.RPAREN)
        return cls(app.symbol, app.sorts, app.args)  # type: ignore

    def left_assoc(self) -> LeftAssoc:
        return self._assoc(TokenType.ML_LEFT_ASSOC, LeftAssoc)

    def right_assoc(self) -> RightAssoc:
        return self._assoc(TokenType.ML_RIGHT_ASSOC, RightAssoc)

    def _attr_list(self) -> list[App]:
        return self._delimited_list_of(self.app, TokenType.LBRACK, TokenType.RBRACK)

    def sentence(self) -> Sentence:
        token_type = self._la.type

        if token_type not in self._SENTENCE_KWS:
            raise ValueError(f'Expected {[kw.name for kw in self._SENTENCE_KWS]}, found: {token_type.name}')

        parse = getattr(self, self._SENTENCE_KWS[token_type])
        return parse()

    def importt(self) -> Import:
        self._match(TokenType.KW_IMPORT)
        module_name = self.id()
        attrs = self._attr_list()
        return Import(module_name, attrs)

    def sort_decl(self) -> SortDecl:
        self._match(TokenType.KW_SORT)
        name = self.id()
        vars = self._sort_var_list()
        attrs = self._attr_list()
        return SortDecl(name, vars, attrs, hooked=False)

    def hooked_sort_decl(self) -> SortDecl:
        self._match(TokenType.KW_HOOKED_SORT)
        name = self.id()
        vars = self._sort_var_list()
        attrs = self._attr_list()
        return SortDecl(name, vars, attrs, hooked=True)

    def _sort_var_list(self) -> list[SortVar]:
        return self._delimited_list_of(self.sort_var, TokenType.LBRACE, TokenType.RBRACE)

    def symbol_decl(self) -> SymbolDecl:
        self._match(TokenType.KW_SYMBOL)
        symbol = self.symbol()
        sort_params = self._sort_param_list()
        self._match(TokenType.COLON)
        sort = self.sort()
        attrs = self._attr_list()
        return SymbolDecl(symbol, sort_params, sort, attrs, hooked=False)

    def hooked_symbol_decl(self) -> SymbolDecl:
        self._match(TokenType.KW_HOOKED_SYMBOL)
        symbol = self.symbol()
        sort_params = self._sort_param_list()
        self._match(TokenType.COLON)
        sort = self.sort()
        attrs = self._attr_list()
        return SymbolDecl(symbol, sort_params, sort, attrs, hooked=True)

    def alias_decl(self) -> AliasDecl:
        self._match(TokenType.KW_ALIAS)
        symbol = self.symbol()
        sort_params = self._sort_param_list()
        self._match(TokenType.COLON)
        sort = self.sort()
        self._match(TokenType.KW_WHERE)
        left = self.app()
        self._match(TokenType.WALRUS)
        right = self.pattern()
        attrs = self._attr_list()
        return AliasDecl(symbol, sort_params, sort, left, right, attrs)

    def _sort_param_list(self) -> list[Sort]:
        return self._delimited_list_of(self.sort, TokenType.LPAREN, TokenType.RPAREN)

    # TODO remove once \left-assoc{}(\or{...}(...)) is no longer supported
    def multi_or(self) -> list[Pattern]:
        self._match(TokenType.ML_LEFT_ASSOC)
        self._match(TokenType.LBRACE)
        self._match(TokenType.RBRACE)
        self._match(TokenType.LPAREN)
        self._match(TokenType.ML_OR)
        self._match(TokenType.LBRACE)
        self.sort()
        self._match(TokenType.RBRACE)
        patterns = self._pattern_list()
        self._match(TokenType.RPAREN)
        return patterns

    def symbol(self) -> Symbol:
        name = self.symbol_id()
        vars = self._sort_var_list()
        return Symbol(name, vars)

    def axiom(self) -> Axiom:
        self._match(TokenType.KW_AXIOM)
        vars = self._sort_var_list()
        pattern = self.pattern()
        attrs = self._attr_list()
        return Axiom(vars, pattern, attrs)

    def claim(self) -> Claim:
        self._match(TokenType.KW_CLAIM)
        vars = self._sort_var_list()
        pattern = self.pattern()
        attrs = self._attr_list()
        return Claim(vars, pattern, attrs)

    def module(self) -> Module:
        self._match(TokenType.KW_MODULE)
        name = self.id()

        sentences: list[Sentence] = []
        while self._la.type != TokenType.KW_ENDMODULE:
            sentences.append(self.sentence())
        self._consume()

        attrs = self._attr_list()

        return Module(name, sentences, attrs)

    def definition(self) -> Definition:
        attrs = self._attr_list()

        modules: list[Module] = []
        while self._la.type != TokenType.EOF:
            modules.append(self.module())

        return Definition(modules, attrs)
