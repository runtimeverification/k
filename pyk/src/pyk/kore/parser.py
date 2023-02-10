from itertools import islice
from typing import Callable, Generic, Iterator, List, Mapping, Type, TypeVar, Union

from ..utils import repeat_last
from .lexer import KoreLexer, KoreToken
from .syntax import (
    DV,
    AliasDecl,
    And,
    App,
    Assoc,
    Axiom,
    BinaryConn,
    BinaryPred,
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
    MLFixpoint,
    MLPattern,
    MLQuant,
    Module,
    Mu,
    Next,
    Not,
    Nu,
    NullaryConn,
    Or,
    Pattern,
    Rewrites,
    RightAssoc,
    RoundPred,
    Sentence,
    Sort,
    SortApp,
    SortDecl,
    SortVar,
    String,
    SVar,
    Symbol,
    SymbolDecl,
    Top,
    UnaryConn,
    VarPattern,
    decode_kore_str,
)

T = TypeVar('T')
NC = TypeVar('NC', bound=NullaryConn)
UC = TypeVar('UC', bound=Union[UnaryConn, Next])
BC = TypeVar('BC', bound=Union[BinaryConn, Rewrites])
QF = TypeVar('QF', bound=MLQuant)
FP = TypeVar('FP', bound=MLFixpoint)
RP = TypeVar('RP', bound=RoundPred)
BP = TypeVar('BP', bound=BinaryPred)
AS = TypeVar('AS', bound=Assoc)


class _LookaheadBuffer(Generic[T]):
    """Circular buffer over an infinite stream"""

    _la: int
    _it: Iterator[T]
    _buf: List[T]
    _pos: int

    def __init__(self, la: int, it: Iterator[T]):
        if la < 1:
            raise ValueError(f'Expected buffer size of at least 1, found: {la}')

        self._la = la
        self._it = it
        self._buf = list(islice(it, la))
        self._pos = 0

    def __call__(self, k: int = 1) -> T:
        return self.lookahead(k)

    def lookahead(self, k: int = 1) -> T:
        if not (1 <= k <= self._la):
            raise ValueError(f'Illegal lookahed value: {k}')

        return self._buf[(self._pos + k - 1) % self._la]

    def consume(self) -> T:
        res = self._buf[self._pos]
        self._buf[self._pos] = next(self._it)
        self._pos = (self._pos + 1) % self._la
        return res


class KoreParser:
    _la: _LookaheadBuffer[KoreToken]

    _ml_symbols: Mapping[KoreToken.Type, Callable[[], MLPattern]]
    _sentence_keywords: Mapping[KoreToken.Type, Callable[[], Sentence]]

    def __init__(self, text: str):
        self._la = _LookaheadBuffer(2, repeat_last(KoreLexer(text)))

        self._ml_symbols = {
            KoreToken.Type.ML_TOP: self.top,
            KoreToken.Type.ML_BOTTOM: self.bottom,
            KoreToken.Type.ML_NOT: self.nott,
            KoreToken.Type.ML_AND: self.andd,
            KoreToken.Type.ML_OR: self.orr,
            KoreToken.Type.ML_IMPLIES: self.implies,
            KoreToken.Type.ML_IFF: self.iff,
            KoreToken.Type.ML_EXISTS: self.exists,
            KoreToken.Type.ML_FORALL: self.forall,
            KoreToken.Type.ML_MU: self.mu,
            KoreToken.Type.ML_NU: self.nu,
            KoreToken.Type.ML_CEIL: self.ceil,
            KoreToken.Type.ML_FLOOR: self.floor,
            KoreToken.Type.ML_EQUALS: self.equals,
            KoreToken.Type.ML_IN: self.inn,
            KoreToken.Type.ML_NEXT: self.next,
            KoreToken.Type.ML_REWRITES: self.rewrites,
            KoreToken.Type.ML_DV: self.dv,
            KoreToken.Type.ML_LEFT_ASSOC: self.left_assoc,
            KoreToken.Type.ML_RIGHT_ASSOC: self.right_assoc,
        }

        self._sentence_kws = {
            KoreToken.Type.KW_IMPORT: self.importt,
            KoreToken.Type.KW_SORT: self.sort_decl,
            KoreToken.Type.KW_HOOKED_SORT: self.hooked_sort_decl,
            KoreToken.Type.KW_SYMBOL: self.symbol_decl,
            KoreToken.Type.KW_HOOKED_SYMBOL: self.hooked_symbol_decl,
            KoreToken.Type.KW_ALIAS: self.alias_decl,
            KoreToken.Type.KW_AXIOM: self.axiom,
            KoreToken.Type.KW_CLAIM: self.claim,
        }

    @property
    def eof(self) -> bool:
        return self._la().type == KoreToken.Type.EOF

    def _consume(self) -> str:
        if self._la().type == KoreToken.Type.EOF:
            raise ValueError('Unexpected EOF')

        return self._la.consume().text

    def _match(self, token_type: KoreToken.Type) -> str:
        if self._la().type != token_type:
            raise ValueError(f'Expected {token_type.name}, found: {self._la().type.name}')

        return self._consume()

    def _delimited_list_of(
        self,
        parse: Callable[[], T],
        ldelim: KoreToken.Type,
        rdelim: KoreToken.Type,
        sep: KoreToken.Type = KoreToken.Type.COMMA,
    ) -> List[T]:
        res: List[T] = []

        self._match(ldelim)
        while self._la().type != rdelim:
            res.append(parse())
            if self._la().type != sep:
                break
            self._consume()
        self._consume()

        return res

    def id(self) -> str:
        return self._match(KoreToken.Type.ID)

    def symbol_id(self) -> str:
        if self._la().type == KoreToken.Type.SYMBOL_ID:
            return self._consume()

        return self._match(KoreToken.Type.ID)

    def _custom_symbol_id(self) -> str:
        symbol = self.symbol_id()

        if symbol in self._ml_symbols:
            raise ValueError(f'Expected custom symbol, found matching logic symbol: {symbol}')

        return symbol

    def _match_symbol_id(self, symbol: str) -> None:
        actual = self.symbol_id()
        if actual != symbol:
            raise ValueError(f'Expected symbol {symbol}, found: {actual}')

    def set_var_id(self) -> str:
        return self._match(KoreToken.Type.SET_VAR_ID)

    def sort(self) -> Sort:
        if self._la(2).type == KoreToken.Type.LBRACE:
            return self.sort_app()

        return self.sort_var()

    def _sort_list(self) -> List[Sort]:
        return self._delimited_list_of(self.sort, KoreToken.Type.LBRACE, KoreToken.Type.RBRACE)

    def sort_var(self) -> SortVar:
        name = self._match(KoreToken.Type.ID)
        return SortVar(name)

    def sort_app(self) -> SortApp:
        name = self._match(KoreToken.Type.ID)
        sorts = self._sort_list()
        return SortApp(name, sorts)

    def pattern(self) -> Pattern:
        if self._la().type == KoreToken.Type.STRING:
            return self.string()

        if self._la().type in self._ml_symbols:
            return self.ml_pattern()

        if self._la(2).type == KoreToken.Type.COLON:
            return self.var_pattern()

        return self.app()

    def _pattern_list(self) -> List[Pattern]:
        return self._delimited_list_of(self.pattern, KoreToken.Type.LPAREN, KoreToken.Type.RPAREN)

    def string(self) -> String:
        value = self._match(KoreToken.Type.STRING)
        return String(decode_kore_str(value[1:-1]))

    def app(self) -> App:
        symbol = self._custom_symbol_id()
        sorts = self._sort_list()
        patterns = self._pattern_list()
        return App(symbol, sorts, patterns)

    def var_pattern(self) -> VarPattern:
        if self._la().type == KoreToken.Type.SET_VAR_ID:
            return self.set_var()

        return self.elem_var()

    def set_var(self) -> SVar:
        name = self._match(KoreToken.Type.SET_VAR_ID)
        self._match(KoreToken.Type.COLON)
        sort = self.sort()
        return SVar(name, sort)

    def elem_var(self) -> EVar:
        name = self._match(KoreToken.Type.ID)
        self._match(KoreToken.Type.COLON)
        sort = self.sort()
        return EVar(name, sort)

    def ml_pattern(self) -> MLPattern:
        token_type = self._la().type
        if token_type not in self._ml_symbols:
            raise ValueError(f'Exected matching logic symbol, found: {self._la().text}')
        parse = self._ml_symbols[token_type]
        return parse()

    def _nullary(self, token_type: KoreToken.Type, cls: Type[NC]) -> NC:
        self._match(token_type)
        self._match(KoreToken.Type.LBRACE)
        sort = self.sort()
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        self._match(KoreToken.Type.RPAREN)
        # TODO Implement NullaryConn.create(symbol, sort) instead
        # TODO Consider MLConn.create(symbol, sort, patterns) as well
        return cls(sort)  # type: ignore

    def top(self) -> Top:
        return self._nullary(KoreToken.Type.ML_TOP, Top)

    def bottom(self) -> Bottom:
        return self._nullary(KoreToken.Type.ML_BOTTOM, Bottom)

    def _unary(self, token_type: KoreToken.Type, cls: Type[UC]) -> UC:
        self._match(token_type)
        self._match(KoreToken.Type.LBRACE)
        sort = self.sort()
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        pattern = self.pattern()
        self._match(KoreToken.Type.RPAREN)
        return cls(sort, pattern)  # type: ignore

    def nott(self) -> Not:
        return self._unary(KoreToken.Type.ML_NOT, Not)

    def _binary(self, token_type: KoreToken.Type, cls: Type[BC]) -> BC:
        self._match(token_type)
        self._match(KoreToken.Type.LBRACE)
        sort = self.sort()
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        left = self.pattern()
        self._match(KoreToken.Type.COMMA)
        right = self.pattern()
        self._match(KoreToken.Type.RPAREN)
        return cls(sort, left, right)  # type: ignore

    def andd(self) -> And:
        return self._binary(KoreToken.Type.ML_AND, And)

    def orr(self) -> Or:
        return self._binary(KoreToken.Type.ML_OR, Or)

    def implies(self) -> Implies:
        return self._binary(KoreToken.Type.ML_IMPLIES, Implies)

    def iff(self) -> Iff:
        return self._binary(KoreToken.Type.ML_IFF, Iff)

    def _quantifier(self, token_type: KoreToken.Type, cls: Type[QF]) -> QF:
        self._match(token_type)
        self._match(KoreToken.Type.LBRACE)
        sort = self.sort()
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        var = self.elem_var()
        self._match(KoreToken.Type.COMMA)
        pattern = self.pattern()
        self._match(KoreToken.Type.RPAREN)
        return cls(sort, var, pattern)  # type: ignore

    def exists(self) -> Exists:
        return self._quantifier(KoreToken.Type.ML_EXISTS, Exists)

    def forall(self) -> Forall:
        return self._quantifier(KoreToken.Type.ML_FORALL, Forall)

    def _fixpoint(self, token_type: KoreToken.Type, cls: Type[FP]) -> FP:
        self._match(token_type)
        self._match(KoreToken.Type.LBRACE)
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        var = self.set_var()
        self._match(KoreToken.Type.COMMA)
        pattern = self.pattern()
        self._match(KoreToken.Type.RPAREN)
        return cls(var, pattern)  # type: ignore

    def mu(self) -> Mu:
        return self._fixpoint(KoreToken.Type.ML_MU, Mu)

    def nu(self) -> Nu:
        return self._fixpoint(KoreToken.Type.ML_NU, Nu)

    def _round_pred(self, token_type: KoreToken.Type, cls: Type[RP]) -> RP:
        self._match(token_type)
        self._match(KoreToken.Type.LBRACE)
        op_sort = self.sort()
        self._match(KoreToken.Type.COMMA)
        sort = self.sort()
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        pattern = self.pattern()
        self._match(KoreToken.Type.RPAREN)
        return cls(op_sort, sort, pattern)  # type: ignore

    def ceil(self) -> Ceil:
        return self._round_pred(KoreToken.Type.ML_CEIL, Ceil)

    def floor(self) -> Floor:
        return self._round_pred(KoreToken.Type.ML_FLOOR, Floor)

    def _binary_pred(self, token_type: KoreToken.Type, cls: Type[BP]) -> BP:
        self._match(token_type)
        self._match(KoreToken.Type.LBRACE)
        left_sort = self.sort()
        self._match(KoreToken.Type.COMMA)
        right_sort = self.sort()
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        left = self.pattern()
        self._match(KoreToken.Type.COMMA)
        right = self.pattern()
        self._match(KoreToken.Type.RPAREN)
        return cls(left_sort, right_sort, left, right)  # type: ignore

    def equals(self) -> Equals:
        return self._binary_pred(KoreToken.Type.ML_EQUALS, Equals)

    def inn(self) -> In:
        return self._binary_pred(KoreToken.Type.ML_IN, In)

    def next(self) -> Next:
        return self._unary(KoreToken.Type.ML_NEXT, Next)

    def rewrites(self) -> Rewrites:
        return self._binary(KoreToken.Type.ML_REWRITES, Rewrites)

    def dv(self) -> DV:
        self._match(KoreToken.Type.ML_DV)
        self._match(KoreToken.Type.LBRACE)
        sort = self.sort()
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        value = self.string()
        self._match(KoreToken.Type.RPAREN)
        return DV(sort, value)

    def _assoc(self, token_type: KoreToken.Type, cls: Type[AS]) -> AS:
        self._match(token_type)
        self._match(KoreToken.Type.LBRACE)
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        app = self.app()
        self._match(KoreToken.Type.RPAREN)
        return cls(app)  # type: ignore

    def left_assoc(self) -> LeftAssoc:
        return self._assoc(KoreToken.Type.ML_LEFT_ASSOC, LeftAssoc)

    def right_assoc(self) -> RightAssoc:
        return self._assoc(KoreToken.Type.ML_RIGHT_ASSOC, RightAssoc)

    def _attr_list(self) -> List[App]:
        return self._delimited_list_of(self.app, KoreToken.Type.LBRACK, KoreToken.Type.RBRACK)

    def sentence(self) -> Sentence:
        token_type = self._la().type

        if token_type not in self._sentence_kws:
            raise ValueError(f'Expected {[kw.name for kw in self._sentence_kws]}, found: {token_type.name}')

        parse = self._sentence_kws[token_type]
        return parse()

    def importt(self) -> Import:
        self._match(KoreToken.Type.KW_IMPORT)
        module_name = self.id()
        attrs = self._attr_list()
        return Import(module_name, attrs)

    def sort_decl(self) -> SortDecl:
        self._match(KoreToken.Type.KW_SORT)
        name = self.id()
        vars = self._sort_var_list()
        attrs = self._attr_list()
        return SortDecl(name, vars, attrs, hooked=False)

    def hooked_sort_decl(self) -> SortDecl:
        self._match(KoreToken.Type.KW_HOOKED_SORT)
        name = self.id()
        vars = self._sort_var_list()
        attrs = self._attr_list()
        return SortDecl(name, vars, attrs, hooked=True)

    def _sort_var_list(self) -> List[SortVar]:
        return self._delimited_list_of(self.sort_var, KoreToken.Type.LBRACE, KoreToken.Type.RBRACE)

    def symbol_decl(self) -> SymbolDecl:
        self._match(KoreToken.Type.KW_SYMBOL)
        symbol = self.symbol()
        sort_params = self._sort_param_list()
        self._match(KoreToken.Type.COLON)
        sort = self.sort()
        attrs = self._attr_list()
        return SymbolDecl(symbol, sort_params, sort, attrs, hooked=False)

    def hooked_symbol_decl(self) -> SymbolDecl:
        self._match(KoreToken.Type.KW_HOOKED_SYMBOL)
        symbol = self.symbol()
        sort_params = self._sort_param_list()
        self._match(KoreToken.Type.COLON)
        sort = self.sort()
        attrs = self._attr_list()
        return SymbolDecl(symbol, sort_params, sort, attrs, hooked=True)

    def alias_decl(self) -> AliasDecl:
        self._match(KoreToken.Type.KW_ALIAS)
        symbol = self.symbol()
        sort_params = self._sort_param_list()
        self._match(KoreToken.Type.COLON)
        sort = self.sort()
        self._match(KoreToken.Type.KW_WHERE)
        left = self.app()
        self._match(KoreToken.Type.WALRUS)
        right = self.pattern()
        attrs = self._attr_list()
        return AliasDecl(symbol, sort_params, sort, left, right, attrs)

    def _sort_param_list(self) -> List[Sort]:
        return self._delimited_list_of(self.sort, KoreToken.Type.LPAREN, KoreToken.Type.RPAREN)

    def symbol(self) -> Symbol:
        name = self.symbol_id()
        vars = self._sort_var_list()
        return Symbol(name, vars)

    def axiom(self) -> Axiom:
        self._match(KoreToken.Type.KW_AXIOM)
        vars = self._sort_var_list()
        pattern = self.pattern()
        attrs = self._attr_list()
        return Axiom(vars, pattern, attrs)

    def claim(self) -> Claim:
        self._match(KoreToken.Type.KW_CLAIM)
        vars = self._sort_var_list()
        pattern = self.pattern()
        attrs = self._attr_list()
        return Claim(vars, pattern, attrs)

    def module(self) -> Module:
        self._match(KoreToken.Type.KW_MODULE)
        name = self.id()

        sentences: List[Sentence] = []
        while self._la().type != KoreToken.Type.KW_ENDMODULE:
            sentences.append(self.sentence())
        self._consume()

        attrs = self._attr_list()

        return Module(name, sentences, attrs)

    def definition(self) -> Definition:
        attrs = self._attr_list()

        modules: List[Module] = []
        while self._la().type != KoreToken.Type.EOF:
            modules.append(self.module())

        return Definition(modules, attrs)
