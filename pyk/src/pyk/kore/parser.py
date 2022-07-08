from dataclasses import dataclass
from enum import Enum, auto
from itertools import chain, islice
from typing import (
    Callable,
    Final,
    Iterator,
    List,
    Mapping,
    Optional,
    Type,
    TypeVar,
    Union,
)

from ..utils import repeat_last
from .syntax import (
    AliasDecl,
    And,
    Apply,
    Attr,
    Axiom,
    BinaryConn,
    Bottom,
    Ceil,
    Claim,
    Definition,
    DomVal,
    ElemVar,
    Equals,
    Exists,
    Floor,
    Forall,
    Iff,
    Implies,
    Import,
    In,
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
    Sentence,
    SetVar,
    Sort,
    SortCons,
    SortDecl,
    SortVar,
    StrLit,
    Symbol,
    SymbolDecl,
    Top,
    UnaryConn,
    VarPattern,
)


@dataclass(frozen=True)
class KoreToken:

    class Type(Enum):
        EOF = 0
        COMMA = auto()
        COLON = auto()
        WALRUS = auto()
        LPAREN = auto()
        RPAREN = auto()
        LBRACE = auto()
        RBRACE = auto()
        LBRACK = auto()
        RBRACK = auto()
        STRING = auto()
        ID = auto()
        SYMBOL_ID = auto()
        SET_VAR_ID = auto()
        KW_MODULE = auto()
        KW_ENDMODULE = auto()
        KW_IMPORT = auto()
        KW_SORT = auto()
        KW_HOOKED_SORT = auto()
        KW_SYMBOL = auto()
        KW_HOOKED_SYMBOL = auto()
        KW_AXIOM = auto()
        KW_CLAIM = auto()
        KW_ALIAS = auto()
        KW_WHERE = auto()

    text: str
    type: Type


class KoreLexer(Iterator[KoreToken]):

    _KEYWORDS: Final = {
        'module': KoreToken.Type.KW_MODULE,
        'endmodule': KoreToken.Type.KW_ENDMODULE,
        'import': KoreToken.Type.KW_IMPORT,
        'sort': KoreToken.Type.KW_SORT,
        'hooked-sort': KoreToken.Type.KW_HOOKED_SORT,
        'symbol': KoreToken.Type.KW_SYMBOL,
        'hooked-symbol': KoreToken.Type.KW_HOOKED_SYMBOL,
        'axiom': KoreToken.Type.KW_AXIOM,
        'claim': KoreToken.Type.KW_CLAIM,
        'alias': KoreToken.Type.KW_ALIAS,
        'where': KoreToken.Type.KW_WHERE,
    }

    _SIMPLE_CHARS: Final = {
        ',': KoreToken.Type.COMMA,
        '(': KoreToken.Type.LPAREN,
        ')': KoreToken.Type.RPAREN,
        '{': KoreToken.Type.LBRACE,
        '}': KoreToken.Type.RBRACE,
        '[': KoreToken.Type.LBRACK,
        ']': KoreToken.Type.RBRACK,
    }

    _ID_FIRST_CHARS: Final = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ')
    _ID_CHARS: Final = set("01234567890'-").union(_ID_FIRST_CHARS)
    _DELIMITERS: Final = set(':/').union(_SIMPLE_CHARS)

    _iter: Iterator[Optional[str]]  # TODO maybe '' can be the sentinel
    _la: Optional[str]
    _done: bool

    def __init__(self, s: str):
        self._iter = iter(chain(s, [None]))
        self._la = next(self._iter)
        self._done = False

    def __next__(self) -> KoreToken:
        while True:
            if self._la is None:
                if self._done:
                    raise StopIteration

                self._done = True
                return self._eof()

            if self._la.isspace():
                self._consume()
                continue

            if self._la == '/':
                self._comment()
                continue

            if self._la in self._SIMPLE_CHARS:
                return self._simple_char()

            if self._la == ':':
                return self._colon_or_walrus()

            if self._la == '"':
                return self._string()

            if self._la == '\\':
                return self._symbol_id()

            if self._la == '@':
                return self._set_var_id()

            if self._la in self._ID_FIRST_CHARS:
                return self._id_or_keyword()

            raise ValueError(f'Unexpected character: {self._la}')

    def _consume(self) -> str:
        if not self._la:
            raise ValueError('Unexpected <EOF>')

        consumed = self._la
        self._la = next(self._iter)
        return consumed

    # TODO _match() for sets of strings
    def _match(self, *cs: str) -> str:
        actual = '<EOF>' if self._la is None else self._la

        if self._la not in cs:
            expected = ', '.join(cs)
            raise ValueError(f'Expected {expected}, found: {actual}')

        return self._consume()

    def _comment(self) -> None:
        self._match('/')
        char = self._match('/', '*')

        if char == '/':
            self._line_comment_rest()
        elif char == '*':
            self._block_comment_rest()
        else:
            assert False

    def _line_comment_rest(self) -> None:
        while self._la is not None and self._la != '\n':
            self._consume()

        if self._la:
            assert self._la == '\n'
            self._consume()

    def _block_comment_rest(self) -> None:
        while True:
            while self._la != '*':
                self._consume()

            self._consume()
            if self._la == '/':
                self._consume()
                break

    def _eof(self) -> KoreToken:
        return KoreToken('', KoreToken.Type.EOF)

    def _simple_char(self) -> KoreToken:
        char = self._match(*self._SIMPLE_CHARS)
        return KoreToken(char, self._SIMPLE_CHARS[char])

    def _colon_or_walrus(self) -> KoreToken:
        self._match(':')

        if self._la == '=':
            self._consume()
            return KoreToken(':=', KoreToken.Type.WALRUS)

        return KoreToken(':', KoreToken.Type.COLON)

    def _string(self) -> KoreToken:
        buf: List[str] = []

        buf += self._match('"')
        while self._la != '"':
            buf += self._consume()
        buf += self._match('"')

        return KoreToken(''.join(buf), KoreToken.Type.STRING)

    def _symbol_id(self) -> KoreToken:
        self._match('\\')
        name = self._id_text()
        return KoreToken(f'\\{name}', KoreToken.Type.SYMBOL_ID)

    def _set_var_id(self) -> KoreToken:
        self._match('@')
        name = self._id_text()
        return KoreToken(f'@{name}', KoreToken.Type.SET_VAR_ID)

    def _id_or_keyword(self) -> KoreToken:
        name = self._id_text()

        if name in self._KEYWORDS:
            return KoreToken(name, self._KEYWORDS[name])

        return KoreToken(name, KoreToken.Type.ID)

    def _id_text(self) -> str:
        buf: List[str] = []
        buf += self._match(*self._ID_FIRST_CHARS)
        while self._la is not None and not self._la.isspace() and self._la not in self._DELIMITERS:
            buf += self._match(*self._ID_CHARS)
        return ''.join(buf)


T = TypeVar('T')
NC = TypeVar('NC', bound=NullaryConn)
UC = TypeVar('UC', bound=Union[UnaryConn, Next])
BC = TypeVar('BC', bound=Union[BinaryConn, Rewrites])
QF = TypeVar('QF', bound=MLQuant)
FP = TypeVar('FP', bound=MLFixpoint)
# TODO Create class RoundPred in syntax.py, define with bound
RP = TypeVar('RP', Ceil, Floor)
# TODO Create class BinaryPred in syntax.py, define with bound
BP = TypeVar('BP', Equals, In)


class KoreParser:
    _LA: Final = 2  # TODO extract class

    _ml_symbols: Mapping[str, Callable[[], MLPattern]]
    _sentence_keywords: Mapping[KoreToken.Type, Callable[[], Sentence]]
    _iter: Iterator[KoreToken]
    _la_buf: List[KoreToken]
    _la_pos: int

    def __init__(self, text: str):
        self._ml_symbols = {
            '\\top': self.top,
            '\\bottom': self.bottom,
            '\\not': self.nott,
            '\\and': self.andd,
            '\\or': self.orr,
            '\\implies': self.implies,
            '\\iff': self.iff,
            '\\exists': self.exists,
            '\\forall': self.forall,
            '\\mu': self.mu,
            '\\nu': self.nu,
            '\\ceil': self.ceil,
            '\\floor': self.floor,
            '\\equals': self.equals,
            '\\in': self.inn,
            '\\next': self.next,
            '\\rewrites': self.rewrites,
            '\\dv': self.dv,
            '\\left-assoc': self._unsupported_ml_symbol('\\left-assoc'),
            '\\right-assoc': self._unsupported_ml_symbol('\\right-assoc'),
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

        self._iter = repeat_last(KoreLexer(text))  # ensures easier handling of the circlar buffer
        self._la_buf = list(islice(self._iter, self._LA))
        self._la_pos = 0

    def _la(self, k=1) -> KoreToken:
        if not (1 <= k <= self._LA):
            raise ValueError(f'Illegal lookahed: {k}')
        return self._la_buf[(self._la_pos + k - 1) % self._LA]

    def _consume(self) -> str:
        if self._la().type == KoreToken.Type.EOF:
            raise ValueError('Unexpected EOF')

        text = self._la_buf[self._la_pos].text
        self._la_buf[self._la_pos] = next(self._iter)
        self._la_pos = (self._la_pos + 1) % self._LA
        return text

    def _match(self, token_type: KoreToken.Type) -> str:
        if self._la().type != token_type:
            raise ValueError(f'Expected {token_type.name}, found: {self._la().type.name}')

        return self._consume()

    def _delimited_list_of(
        self,
        parse: Callable[[], T],
        ldelim: KoreToken.Type,
        rdelim: KoreToken.Type,
        sep=KoreToken.Type.COMMA,
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

    def set_var_id(self) -> str:
        return self._match(KoreToken.Type.SET_VAR_ID)

    def sort(self) -> Sort:
        if self._la(2).type == KoreToken.Type.LBRACE:
            return self.sort_cons()

        return self.sort_var()

    def _sort_list(self) -> List[Sort]:
        return self._delimited_list_of(self.sort, KoreToken.Type.LBRACE, KoreToken.Type.RBRACE)

    def sort_var(self) -> SortVar:
        name = self._match(KoreToken.Type.ID)
        return SortVar(name)

    def sort_cons(self) -> SortCons:
        name = self._match(KoreToken.Type.ID)
        sorts = self._sort_list()
        return SortCons(name, sorts)

    def pattern(self) -> Pattern:
        if self._la().type == KoreToken.Type.STRING:
            return self.str_lit()

        if self._la().type == KoreToken.Type.SYMBOL_ID and self._la().text in self._ml_symbols:
            return self.ml_pattern()

        if self._la(2).type == KoreToken.Type.COLON:
            return self.var_pattern()

        return self.apply()

    def _pattern_list(self) -> List[Pattern]:
        return self._delimited_list_of(self.pattern, KoreToken.Type.LPAREN, KoreToken.Type.RPAREN)

    def str_lit(self) -> StrLit:
        value = self._match(KoreToken.Type.STRING)
        return StrLit(value[1:-1])

    def apply(self) -> Apply:
        symbol = self.symbol_id()
        sorts = self._sort_list()
        patterns = self._pattern_list()
        return Apply(symbol, sorts, patterns)

    def var_pattern(self) -> VarPattern:
        if self._la().type == KoreToken.Type.SET_VAR_ID:
            return self.set_var()

        return self.elem_var()

    def set_var(self) -> SetVar:
        name = self._match(KoreToken.Type.SET_VAR_ID)
        self._match(KoreToken.Type.COLON)
        sort = self.sort()
        return SetVar(name, sort)

    def elem_var(self) -> ElemVar:
        name = self._match(KoreToken.Type.ID)
        self._match(KoreToken.Type.COLON)
        sort = self.sort()
        return ElemVar(name, sort)

    def ml_pattern(self) -> MLPattern:
        if self._la().type != KoreToken.Type.SYMBOL_ID:
            raise ValueError(f'Expected SYMBOL_ID, found: {self._la().type.name}')

        symbol = self._la().text
        if symbol not in self._ml_symbols:
            raise ValueError(f'Exected matching logic symbol, found: {self._la().text}')

        parse = self._ml_symbols[symbol]
        return parse()

    def _unsupported_ml_symbol(self, symbol: str) -> Callable[[], MLPattern]:
        def parse():
            raise ValueError(f'Unsupported matching logic symbol: {symbol}')

        return parse

    def _nullary(self, symbol: str, cls: Type[NC]) -> NC:
        # TODO Extract logic
        actual = self.symbol_id()
        if symbol != actual:
            raise ValueError(f'Expected {symbol}, found: {actual}')

        self._match(KoreToken.Type.LBRACE)
        sort = self.sort()
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        self._match(KoreToken.Type.RPAREN)
        # TODO Implement NullaryConn.create(symbol, sort) instead
        # TODO Consider MLConn.create(symbol, sort, patterns) as well
        return cls(sort)  # type: ignore

    def top(self) -> Top:
        return self._nullary('\\top', Top)

    def bottom(self) -> Bottom:
        return self._nullary('\\bottom', Bottom)

    def _unary(self, symbol: str, cls: Type[UC]) -> UC:
        actual = self.symbol_id()
        if symbol != actual:
            raise ValueError(f'Expected {symbol}, found: {actual}')

        self._match(KoreToken.Type.LBRACE)
        sort = self.sort()
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        pattern = self.pattern()
        self._match(KoreToken.Type.RPAREN)
        return cls(sort, pattern)  # type: ignore

    def nott(self) -> Not:
        return self._unary('\\not', Not)

    def _binary(self, symbol: str, cls: Type[BC]) -> BC:
        actual = self.symbol_id()
        if symbol != actual:
            raise ValueError(f'Expected {symbol}, found: {actual}')

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
        return self._binary('\\and', And)

    def orr(self) -> Or:
        return self._binary('\\or', Or)

    def implies(self) -> Implies:
        return self._binary('\\implies', Implies)

    def iff(self) -> Iff:
        return self._binary('\\iff', Iff)

    def _quantifier(self, symbol: str, cls: Type[QF]) -> QF:
        actual = self.symbol_id()
        if symbol != actual:
            raise ValueError(f'Expected {symbol}, found: {actual}')

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
        return self._quantifier('\\exists', Exists)

    def forall(self) -> Forall:
        return self._quantifier('\\forall', Forall)

    def _fixpoint(self, symbol: str, cls: Type[FP]) -> FP:
        actual = self.symbol_id()
        if symbol != actual:
            raise ValueError(f'Expected {symbol}, found: {actual}')

        self._match(KoreToken.Type.LBRACE)
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        var = self.set_var()
        self._match(KoreToken.Type.COMMA)
        pattern = self.pattern()
        self._match(KoreToken.Type.RPAREN)
        return cls(var, pattern)  # type: ignore

    def mu(self) -> Mu:
        return self._fixpoint('\\mu', Mu)

    def nu(self) -> Nu:
        return self._fixpoint('\\nu', Nu)

    def _round_pred(self, symbol: str, cls: Type[RP]) -> RP:
        actual = self.symbol_id()
        if symbol != actual:
            raise ValueError(f'Expected {symbol}, found: {actual}')

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
        return self._round_pred('\\ceil', Ceil)

    def floor(self) -> Floor:
        return self._round_pred('\\floor', Floor)

    def _binary_pred(self, symbol: str, cls: Type[BP]) -> BP:
        actual = self.symbol_id()
        if symbol != actual:
            raise ValueError(f'Expected {symbol}, found: {actual}')

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
        return self._binary_pred('\\equals', Equals)

    def inn(self) -> In:
        return self._binary_pred('\\in', In)

    def next(self) -> Next:
        return self._unary('\\next', Next)

    def rewrites(self) -> Rewrites:
        return self._binary('\\rewrites', Rewrites)

    def dv(self) -> DomVal:
        symbol = self.symbol_id()
        if symbol != '\\dv':
            raise ValueError(f'Expected \\dv, found: {symbol}')

        self._match(KoreToken.Type.LBRACE)
        sort = self.sort()
        self._match(KoreToken.Type.RBRACE)
        self._match(KoreToken.Type.LPAREN)
        value = self.str_lit()
        self._match(KoreToken.Type.RPAREN)
        return DomVal(sort, value)

    def attr(self) -> Attr:
        symbol = self.symbol_id()  # TODO ensure not ml_symbol: custom_symbol() perhaps?
        self._match(KoreToken.Type.LBRACE)
        self._match(KoreToken.Type.RBRACE)
        params = self._attr_param_list()
        return Attr(symbol, params)

    def _attr_param(self) -> Union[StrLit, Attr]:
        if self._la().type == KoreToken.Type.STRING:
            return self.str_lit()

        return self.attr()

    def _attr_param_list(self) -> List[Union[StrLit, Attr]]:
        return self._delimited_list_of(self._attr_param, KoreToken.Type.LPAREN, KoreToken.Type.RPAREN)

    def _attr_list(self) -> List[Attr]:
        return self._delimited_list_of(self.attr, KoreToken.Type.LBRACK, KoreToken.Type.RBRACK)

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
        left = self.apply()
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
