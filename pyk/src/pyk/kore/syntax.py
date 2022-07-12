import json
from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import IntEnum
from itertools import chain
from typing import (
    Any,
    ClassVar,
    Dict,
    Final,
    Iterable,
    Iterator,
    List,
    Mapping,
    Optional,
    Tuple,
    Type,
    TypeVar,
    Union,
    final,
)

KEYWORDS: Final = {
    "module",
    "endmodule",
    "import",
    "sort",
    "hooked-sort",
    "symbol",
    "hooked-symbol",
    "axiom",
    "claim",
    "alias",
    "where",
}


_A_TO_Z_LC: Final = 'abcdefghijklmnopqrstuvwxyz'
_A_TO_Z_UC: Final = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
_0_TO_9: Final = '0123456789'

_ID_FST_CHR = set(_A_TO_Z_LC + _A_TO_Z_UC)
_ID_CHR = set(_0_TO_9 + "'-").union(_ID_FST_CHR)


def _has_id_syntax(s: str) -> bool:
    return len(s) > 0 and s[0] in _ID_FST_CHR and all(c in _ID_CHR for c in s[1:])


def is_id(s: str) -> bool:
    return _has_id_syntax(s) and s not in KEYWORDS


def is_symbol_id(s: str) -> bool:
    if len(s) < 1:
        return False

    if s[0] == '\\':
        return _has_id_syntax(s[1:])

    return is_id(s)


def is_set_var_id(s: str) -> bool:
    if len(s) < 1:
        return False

    if s[0] != '@':
        return False

    return _has_id_syntax(s[1:])


def check_id(s: str) -> None:
    if not is_id(s):
        raise ValueError(f'Expected identifier, found: {s}')


def check_symbol_id(s: str) -> None:
    if not is_symbol_id(s):
        raise ValueError(f'Expected symbol identifier, found: {s}')


def check_set_var_id(s: str) -> None:
    if not is_set_var_id(s):
        raise ValueError(f'Expected set variable identifier, found: {s}')


def _bracketed(elems: Iterable[str], lbrac: str, rbrac: str) -> str:
    elems = tuple(elems)
    return lbrac + ' ' + ', '.join(elems) + (' ' if elems else '') + rbrac


def _braced(elems: Iterable[str]) -> str:
    return _bracketed(elems, '{', '}')


def _brackd(elems: Iterable[str]) -> str:
    return _bracketed(elems, '[', ']')


def _parend(elems: Iterable[str]) -> str:
    return _bracketed(elems, '(', ')')


# TODO @overload


T = TypeVar('T', bound='Kore')


def unimplemented() -> Any:
    raise RuntimeError('Unimplemented operation')


def unsupported() -> Any:
    raise RuntimeError('Unsupported operation')


class Kore(ABC):
    _TAGS: Final[Mapping[str, str]] = {
        'SortVariable': 'SortVar',
        'SortApp': 'SortCons',
        'EVar': 'ElemVar',
        'SVar': 'SetVar',
        'String': 'StrLit',
        'App': 'Apply',
        'dv': 'DomVal',
        **{k: k for k in (
            'Top',
            'Bottom',
            'Not',
            'And',
            'Or',
            'Implies',
            'Iff',
            'Exists',
            'Forall',
            'Mu',
            'Nu',
            'Ceil',
            'Floor',
            'Equals',
            'In',
            'Next',
            'Rewrites',
        )},
    }

    @classmethod
    @property
    @abstractmethod
    def _tag(cls):
        ...

    @classmethod
    def from_dict(cls: Type[T], dct: Mapping[str, Any]) -> T:
        tag = cls._get_tag(dct)
        if tag not in cls._TAGS:
            raise ValueError(f"Expected Kore tag, found: {tag}")
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)

    @classmethod
    def from_json(cls: Type[T], s: str) -> T:
        return (cls.from_dict(json.loads(s)))

    @staticmethod
    def _get_tag(dct: Mapping[str, Any]) -> str:
        if 'tag' not in dct:
            raise ValueError("Attribute 'tag' is missing")
        return dct['tag']

    @classmethod
    def _check_tag(cls: Type[T], dct: Mapping[str, Any]) -> None:
        tag = cls._get_tag(dct)
        if tag != cls._tag:
            raise ValueError(f"Expected '{cls._tag}' as 'tag' value, found: '{tag}'")

    @property
    def json(self) -> str:
        return json.dumps(self.dict, sort_keys=True)

    @property
    @abstractmethod
    def dict(self) -> Dict[str, Any]:
        ...

    @property
    @abstractmethod
    def text(self) -> str:
        ...


class StrLitLexer(Iterator[Tuple[str, 'StrLitLexer.TokenType']]):

    class TokenType(IntEnum):
        ASCII = 1
        ESC = 2
        UTF_8 = 3
        UTF_16 = 4
        UTF_32 = 5

    _iter: Iterator[Optional[str]]
    _la: Optional[str]

    def __init__(self, s: str):
        self._iter = iter(chain(s, [None]))
        self._la = next(self._iter)

    def __next__(self) -> Tuple[str, TokenType]:
        if self._la is None:
            raise StopIteration()

        if self._la == '"':
            raise ValueError('Unexpected character: "')

        if self._la == '\\':
            return self._escape_sequence()

        return self._printable_ascii_char()

    def _escape_sequence(self) -> Tuple[str, TokenType]:
        assert self._la is not None
        assert self._la == '\\'

        self._match('\\')

        if self._la in {'t', 'n', 'f', 'r', '"', '\\'}:
            token = f'\\{self._la}'
            self._consume()
            return token, self.TokenType.ESC

        hexa_params = {
            'x': (2, lambda x: None, self.TokenType.UTF_8),
            'u': (4, self._validate_utf_16, self.TokenType.UTF_16),
            'U': (8, self._validate_utf_32, self.TokenType.UTF_32),
        }

        if self._la in hexa_params:
            char = self._la
            self._consume()
            nr_digits, validate, token_type = hexa_params[char]
            hexa = self._match_hexa(nr_digits)
            validate(hexa)
            token = f'\\x{hexa}'
            return token, token_type

        raise ValueError(f'Unexpected character: {self._la}')

    @staticmethod
    def _validate_utf_16(hexa: str) -> None:
        if 0xD800 <= int(hexa, 16) <= 0xDFFF:
            raise ValueError(f'Illegal UTF-16 code point: {hexa}')

    @staticmethod
    def _validate_utf_32(hexa: str) -> None:
        StrLitLexer._validate_utf_16(hexa)

        if int(hexa, 16) > 0x10FFFF:
            raise ValueError(f'Illegal UTF-32 code point: {hexa}')

    def _printable_ascii_char(self) -> Tuple[str, TokenType]:
        assert self._la is not None
        assert self._la != '"'
        assert self._la != '\\'

        if not (32 <= ord(self._la) <= 126):
            raise ValueError(f'Expected printable ASCII character, found: character with code {ord(self._la)}')

        token = self._la
        self._consume()
        return token, self.TokenType.ASCII

    def _match(self, c: str) -> None:
        actual = '<EOF>' if self._la is None else self._la

        if self._la != c:
            raise ValueError(f'Expected {c}, found: {actual}')

        self._consume()

    def _consume(self) -> None:
        assert self._la is not None
        self._la = next(self._iter)

    def _match_hexa(self, length: int) -> str:
        if length < 0:
            raise ValueError(f'Expected nonnegative length, got: {length}')

        chars: List[str] = []
        for _ in range(length):
            actual = '<EOF>' if self._la is None else self._la

            if self._la not in set('0123456789abcdefABCDEF'):
                raise ValueError(f'Expected hexadecimal digit, found: {actual}')

            chars += self._la
            self._consume()

        return ''.join(chars)


class Sort(Kore, ABC):
    _SORT_TAGS: Final = {'SortVariable', 'SortApp'}

    name: str

    @classmethod
    def from_dict(cls: Type['Sort'], dct: Mapping[str, Any]) -> 'Sort':
        tag = cls._get_tag(dct)
        if tag not in cls._SORT_TAGS:
            raise ValueError(f'Expected Sort tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)


@final
@dataclass(frozen=True)
class SortVar(Sort):
    _tag = 'SortVariable'  # TODO Haskell: SortVar would be more consistent with SortApp, EVar

    name: str

    def __init__(self, name: str):
        check_id(name)
        object.__setattr__(self, 'name', name)

    @classmethod
    def from_dict(cls: Type['SortVar'], dct: Mapping[str, Any]) -> 'SortVar':
        cls._check_tag(dct)
        return SortVar(name=dct['name'])

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()

    @property
    def text(self) -> str:
        return self.name


@final
@dataclass(frozen=True)
class SortCons(Sort):
    _tag = 'SortApp'

    name: str
    sorts: Tuple[Sort, ...]

    def __init__(self, name: str, sorts: Iterable[Sort] = ()):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sorts', tuple(sorts))

    @classmethod
    def from_dict(cls: Type['SortCons'], dct: Mapping[str, Any]) -> 'SortCons':
        cls._check_tag(dct)
        return SortCons(name=dct['name'], sorts=(Sort.from_dict(arg) for arg in dct['args']))

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()

    @property
    def text(self) -> str:
        return self.name + ' ' + _braced(sort.text for sort in self.sorts)


class Pattern(Kore, ABC):
    _PATTERN_TAGS: Final = {
        'EVar', 'SVar', 'String', 'App', 'Top', 'Bottom', 'Not', 'And', 'Or',
        'Implies', 'Iff', 'Exists', 'Forall', 'Mu', 'Nu', 'Ceil', 'Floor',
        'Equals', 'In', 'Next', 'Rewrites', 'dv',
    }

    @classmethod
    def from_dict(cls: Type['Pattern'], dct: Mapping[str, Any]) -> 'Pattern':
        # TODO extract logic
        tag = cls._get_tag(dct)
        if tag not in cls._PATTERN_TAGS:
            raise ValueError(f'Expected Pattern tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)


class VarPattern(Pattern, ABC):
    _VAR_PATTERN_TAGS: Final = {'EVar', 'SVar'}

    name: str
    sort: Sort

    @classmethod
    def from_dict(cls: Type['VarPattern'], dct: Mapping[str, Any]) -> 'VarPattern':
        tag = cls._get_tag(dct)
        if tag not in cls._PATTERN_TAGS:
            raise ValueError(f'Expected VarPattern tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)

    @property
    def text(self) -> str:
        return f'{self.name} : {self.sort.text}'


@final
@dataclass(frozen=True)
class ElemVar(VarPattern):
    _tag = 'EVar'

    name: str
    sort: Sort

    def __init__(self, name: str, sort: Sort):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sort', sort)

    @classmethod
    def from_dict(cls: Type['ElemVar'], dct: Mapping[str, Any]) -> 'ElemVar':
        cls._check_tag(dct)
        return ElemVar(name=dct['name'], sort=Sort.from_dict(dct['sort']))

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


@final
@dataclass(frozen=True)
class SetVar(VarPattern):
    _tag = 'SVar'

    name: str
    sort: Sort

    def __init__(self, name: str, sort: Sort):
        check_set_var_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sort', sort)

    @classmethod
    def from_dict(cls: Type['SetVar'], dct: Mapping[str, Any]) -> 'SetVar':
        cls._check_tag(dct)
        return SetVar(name=dct['name'], sort=Sort.from_dict(dct['sort']))

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


@final
@dataclass(frozen=True)
class StrLit(Pattern):
    _tag = 'String'

    value: str

    def __init__(self, value: str):
        for _ in StrLitLexer(value):
            pass  # validate value

        object.__setattr__(self, 'value', value)

    @classmethod
    def from_dict(cls: Type['StrLit'], dct: Mapping[str, Any]) -> 'StrLit':
        cls._check_tag(dct)
        return StrLit(value=dct['value'])

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()

    @property
    def text(self) -> str:
        return f'"{self.value}"'

    @property
    def decoded(self) -> str:
        return bytes(self.value, 'ascii').decode('unicode-escape')


@final
@dataclass(frozen=True)
class Apply(Pattern):
    _tag = 'App'  # TODO Haskell: Are there tests for this?

    symbol: str
    sorts: Tuple[Sort, ...]
    patterns: Tuple[Pattern, ...]

    def __init__(self, symbol: str, sorts: Iterable[Sort], patterns: Iterable[Pattern]):
        check_symbol_id(symbol)
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'sorts', tuple(sorts))
        object.__setattr__(self, 'patterns', tuple(patterns))

    @classmethod
    def from_dict(cls: Type['Apply'], dct: Mapping[str, Any]) -> 'Apply':
        cls._check_tag(dct)
        return Apply(
            symbol=dct['name'],
            sorts=(Sort.from_dict(sort) for sort in dct['sorts']),
            patterns=(Pattern.from_dict(arg) for arg in dct['args']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()

    @property
    def text(self) -> str:
        return self.symbol + ' ' + _braced(sort.text for sort in self.sorts) + ' ' + _parend(pattern.text for pattern in self.patterns)


class MLPattern(Pattern, ABC):
    _ML_PATTERN_TAGS: Final = {
        'Top', 'Bottom', 'Not', 'And', 'Or', 'Implies', 'Iff', 'Exists',
        'Forall', 'Mu', 'Nu', 'Ceil', 'Floor', 'Equals', 'In', 'Next',
        'Rewrites', 'dv',
    }

    @classmethod
    @property
    @abstractmethod
    def _symbol(cls):
        ...

    @classmethod
    def from_dict(cls: Type['MLPattern'], dct: Mapping[str, Any]) -> 'MLPattern':
        tag = cls._get_tag(dct)
        if tag not in cls._ML_PATTERN_TAGS:
            raise ValueError(f'Expected MLPattern tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)


class MLConn(MLPattern, ABC):
    _ML_CONN_TAGS: Final = {'Top', 'Bottom', 'Not', 'And', 'Or', 'Implies', 'Iff'}

    sort: Sort

    @property
    @abstractmethod
    def patterns(self) -> Tuple[Pattern, ...]:
        ...

    @classmethod
    def from_dict(cls: Type['MLConn'], dct: Mapping[str, Any]) -> 'MLConn':
        tag = cls._get_tag(dct)
        if tag not in cls._ML_CONN_TAGS:
            raise ValueError(f'Expected MLConn tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)

    @property
    def text(self) -> str:
        return self._symbol + ' { ' + self.sort.text + ' } ' + _parend(pattern.text for pattern in self.patterns)


class NullaryConn(MLConn, ABC):
    _NULLARY_CONN_TAGS: Final = {'Top', 'Bottom'}

    @classmethod
    def from_dict(cls: Type['NullaryConn'], dct: Mapping[str, Any]) -> 'NullaryConn':
        tag = cls._get_tag(dct)
        if tag not in cls._NULLARY_CONN_TAGS:
            raise ValueError(f'Expected NullaryConn tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)

    @property
    def patterns(self) -> Tuple[Pattern, ...]:
        return ()


@final
@dataclass(frozen=True)
class Top(NullaryConn):
    _tag = 'Top'
    _symbol = '\\top'

    sort: Sort

    @classmethod
    def from_dict(cls: Type['Top'], dct: Mapping[str, Any]) -> 'Top':
        cls._check_tag(dct)
        return Top(sort=Sort.from_dict(dct['sort']))

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


@final
@dataclass(frozen=True)
class Bottom(NullaryConn):
    _tag = 'Bottom'
    _symbol = '\\bottom'

    sort: Sort

    @classmethod
    def from_dict(cls: Type['Bottom'], dct: Mapping[str, Any]) -> 'Bottom':
        cls._check_tag(dct)
        return Bottom(sort=Sort.from_dict(dct['sort']))

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


class UnaryConn(MLConn, ABC):
    _UNARY_CONN_TAGS: Final = {'Not'}

    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['UnaryConn'], dct: Mapping[str, Any]) -> 'UnaryConn':
        tag = cls._get_tag(dct)
        if tag not in cls._UNARY_CONN_TAGS:
            raise ValueError(f'Expected UnaryConn tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)

    @property
    def patterns(self) -> Tuple[Pattern, ...]:
        return (self.pattern,)


@final
@dataclass(frozen=True)
class Not(UnaryConn):
    _tag = 'Not'
    _symbol = '\\not'

    sort: Sort
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['Not'], dct: Mapping[str, Any]) -> 'Not':
        cls._check_tag(dct)
        return Not(sort=Sort.from_dict(dct['sort']), pattern=Pattern.from_dict(dct['arg']))

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


class BinaryConn(MLConn, ABC):
    _BINARY_CONN_TAGS: Final = {'And', 'Or', 'Implies', 'Iff'}

    left: Pattern
    right: Pattern

    def __iter__(self) -> Iterator[Pattern]:
        yield self.left
        yield self.right

    @classmethod
    def from_dict(cls: Type['BinaryConn'], dct: Mapping[str, Any]) -> 'BinaryConn':
        tag = cls._get_tag(dct)
        if tag not in cls._BINARY_CONN_TAGS:
            raise ValueError(f'Expected BinaryConn tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)

    @property
    def patterns(self) -> Tuple[Pattern, ...]:
        return (self.left, self.right)


@final
@dataclass(frozen=True)
class And(BinaryConn):
    _tag = 'And'
    _symbol = '\\and'

    sort: Sort
    left: Pattern
    right: Pattern

    @classmethod
    def from_dict(cls: Type['And'], dct: Mapping[str, Any]) -> 'And':
        # TODO Consider implementing in BinaryConn
        cls._check_tag(dct)
        return And(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


@final
@dataclass(frozen=True)
class Or(BinaryConn):
    _tag = 'Or'
    _symbol = '\\or'

    sort: Sort
    left: Pattern
    right: Pattern

    @classmethod
    def from_dict(cls: Type['Or'], dct: Mapping[str, Any]) -> 'Or':
        cls._check_tag(dct)
        return Or(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


@final
@dataclass(frozen=True)
class Implies(BinaryConn):
    _tag = 'Implies'
    _symbol = '\\implies'

    sort: Sort
    left: Pattern
    right: Pattern

    @classmethod
    def from_dict(cls: Type['Implies'], dct: Mapping[str, Any]) -> 'Implies':
        cls._check_tag(dct)
        return Implies(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


@final
@dataclass(frozen=True)
class Iff(BinaryConn):
    _tag = 'Iff'
    _symbol = '\\iff'

    sort: Sort
    left: Pattern
    right: Pattern

    @classmethod
    def from_dict(cls: Type['Iff'], dct: Mapping[str, Any]) -> 'Iff':
        cls._check_tag(dct)
        return Iff(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


class MLQuant(MLPattern, ABC):
    _ML_QUANT_TAGS: Final = {'Exists', 'Forall'}

    sort: Sort
    var: ElemVar
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['MLQuant'], dct: Mapping[str, Any]) -> 'MLQuant':
        tag = cls._get_tag(dct)
        if tag not in cls._ML_QUANT_TAGS:
            raise ValueError(f'Expected MLQuant tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)

    @property
    def text(self) -> str:
        return self._symbol + ' { ' + self.sort.text + ' } ' + _parend((self.var.text, self.pattern.text))


@final
@dataclass(frozen=True)
class Exists(MLQuant):
    _tag = 'Exists'
    _symbol = '\\exists'

    sort: Sort
    var: ElemVar
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['Exists'], dct: Mapping[str, Any]) -> 'Exists':
        cls._check_tag(dct)
        return Exists(
            sort=Sort.from_dict(dct['sort']),
            var=ElemVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),  # TODO Haskell: ElemVar.from_dict(...) would be nicer
            pattern=Pattern.from_dict(dct['arg']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


@final
@dataclass(frozen=True)
class Forall(MLQuant):
    _tag = 'Forall'
    _symbol = '\\forall'

    sort: Sort
    var: ElemVar
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['Forall'], dct: Mapping[str, Any]) -> 'Forall':
        cls._check_tag(dct)
        return Forall(
            sort=Sort.from_dict(dct['sort']),
            var=ElemVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),  # TODO Haskell: ElemVar.from_dict(...) would be nicer
            pattern=Pattern.from_dict(dct['arg']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


class MLFixpoint(MLPattern, ABC):
    _ML_FIXPOINT_TAGS: Final = {'Mu', 'Nu'}

    var: SetVar
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['MLFixpoint'], dct: Mapping[str, Any]) -> 'MLFixpoint':
        tag = cls._get_tag(dct)
        if tag not in cls._ML_FIXPOINT_TAGS:
            raise ValueError(f'Expected MLFixpoint tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)

    @property
    def text(self) -> str:
        return self._symbol + ' { } ' + _parend((self.var.text, self.pattern.text))


@final
@dataclass(frozen=True)
class Mu(MLFixpoint):
    _tag = 'Mu'
    _symbol = '\\mu'

    var: SetVar
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['Mu'], dct: Mapping[str, Any]) -> 'Mu':
        cls._check_tag(dct)
        return Mu(
            var=SetVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),  # TODO SetVar.from_dict(...) would be nicer
            pattern=Pattern.from_dict(dct['arg']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


@final
@dataclass(frozen=True)
class Nu(MLFixpoint):
    _tag = 'Nu'
    _symbol = '\\nu'

    var: SetVar
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['Nu'], dct: Mapping[str, Any]) -> 'Nu':
        cls._check_tag(dct)
        return Nu(
            var=SetVar(name=dct['var'], sort=Sort.from_dict(dct['varSort'])),  # TODO Haskell: SetVar.from_dict(...) would be nicer
            pattern=Pattern.from_dict(dct['arg']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


class MLPred(MLPattern, ABC):
    _ML_PRED_TAGS: Final = {'Ceil', 'Floor', 'Equals', 'In'}

    @classmethod
    def from_dict(cls: Type['MLPred'], dct: Mapping[str, Any]) -> 'MLPred':
        tag = cls._get_tag(dct)
        if tag not in cls._ML_PRED_TAGS:
            raise ValueError(f'Expected MLPred tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)


class RoundPred(MLPred, ABC):
    _ROUND_PRED_TAGS: Final = {'Ceil', 'Floor'}

    op_sort: Sort
    sort: Sort
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['RoundPred'], dct: Mapping[str, Any]) -> 'RoundPred':
        tag = cls._get_tag(dct)
        if tag not in cls._ROUND_PRED_TAGS:
            raise ValueError(f'Expected RoundPred tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)

    @property
    def text(self) -> str:
        return self._symbol + ' ' + _braced((self.op_sort.text, self.sort.text)) + ' ( ' + self.pattern.text + ' )'


@final
@dataclass(frozen=True)
class Ceil(RoundPred):
    _tag = 'Ceil'
    _symbol = '\\ceil'

    op_sort: Sort
    sort: Sort
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['Ceil'], dct: Mapping[str, Any]) -> 'Ceil':
        cls._check_tag(dct)
        return Ceil(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['resultSort']),
            pattern=Pattern.from_dict(dct['arg']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


@final
@dataclass(frozen=True)
class Floor(RoundPred):
    _tag = 'Floor'
    _symbol = '\\floor'

    op_sort: Sort
    sort: Sort
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['Floor'], dct: Mapping[str, Any]) -> 'Floor':
        cls._check_tag(dct)
        return Floor(
            op_sort=Sort.from_dict(dct['argSort']),
            sort=Sort.from_dict(dct['resultSort']),
            pattern=Pattern.from_dict(dct['arg']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


class BinaryPred(MLPred, ABC):
    _BINARY_PRED_TAGS: Final = {'Equals', 'In'}

    left_sort: Sort
    right_sort: Sort
    left: Pattern
    right: Pattern

    @classmethod
    def from_dict(cls: Type['BinaryPred'], dct: Mapping[str, Any]) -> 'BinaryPred':
        tag = cls._get_tag(dct)
        if tag not in cls._BINARY_PRED_TAGS:
            raise ValueError(f'Expected BinaryPred tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)

    @property
    def text(self) -> str:
        return ' '.join([
            self._symbol,
            _braced((self.left_sort.text, self.right_sort.text)),
            _parend((self.left.text, self.right.text)),
        ])


@final
@dataclass(frozen=True)
class Equals(BinaryPred):
    _tag = 'Equals'
    _symbol = '\\equals'

    left_sort: Sort
    right_sort: Sort
    left: Pattern
    right: Pattern

    @classmethod
    def from_dict(cls: Type['Equals'], dct: Mapping[str, Any]) -> 'Equals':
        cls._check_tag(dct)
        return Equals(
            left_sort=Sort.from_dict(dct['argSort']),      # TODO Haskell: Shouldn't this be firstSort instead?
            right_sort=Sort.from_dict(dct['resultSort']),  # TODO Haskell: Shoulnd't this be secondSort instead?
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


@final
@dataclass(frozen=True)
class In(BinaryPred):
    _tag = 'In'
    _symbol = '\\in'

    left_sort: Sort
    right_sort: Sort
    left: Pattern
    right: Pattern

    @classmethod
    def from_dict(cls: Type['In'], dct: Mapping[str, Any]) -> 'In':
        cls._check_tag(dct)
        return In(
            left_sort=Sort.from_dict(dct['argSort']),      # TODO Haskell: Shouldn't this be firstSort instead?
            right_sort=Sort.from_dict(dct['resultSort']),  # TODO Haskell: Shoulnd't this be secondSort instead?
            left=Pattern.from_dict(dct['first']),
            right=Pattern.from_dict(dct['second']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()


class MLRewrite(MLPattern, ABC):
    _ML_REWRITE_TAGS: Final = {'Next', 'Rewrites'}

    sort: Sort

    @classmethod
    def from_dict(cls: Type['MLRewrite'], dct: Mapping[str, Any]) -> 'MLRewrite':
        tag = cls._get_tag(dct)
        if tag not in cls._ML_REWRITE_TAGS:
            raise ValueError(f'Expected MLRewrite tag, found: {tag}')
        cls_id = cls._TAGS[tag]
        return globals()[cls_id].from_dict(dct)


@final
@dataclass(frozen=True)
class Next(MLRewrite):
    _tag = 'Next'
    _symbol = '\\next'

    sort: Sort
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['Next'], dct: Mapping[str, Any]) -> 'Next':
        cls._check_tag(dct)
        return Next(
            sort=Sort.from_dict(dct['sort']),
            pattern=Pattern.from_dict(dct['dest']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()

    @property
    def text(self) -> str:
        return self._symbol + ' { ' + self.sort.text + ' } ( ' + self.pattern.text + ' )'


@final
@dataclass(frozen=True)
class Rewrites(MLRewrite):
    _tag = 'Rewrites'
    _symbol = '\\rewrites'

    sort: Sort
    left: Pattern
    right: Pattern

    @classmethod
    def from_dict(cls: Type['Rewrites'], dct: Mapping[str, Any]) -> 'Rewrites':
        cls._check_tag(dct)
        return Rewrites(
            sort=Sort.from_dict(dct['sort']),
            left=Pattern.from_dict(dct['source']),
            right=Pattern.from_dict(dct['dest']),
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()

    @property
    def text(self) -> str:
        return self._symbol + ' { ' + self.sort.text + ' } ' + _parend((self.left.text, self.right.text))


@final
@dataclass(frozen=True)
class DomVal(MLPattern):
    _tag = 'dv'  # TODO Haskell: Consider 'DV' as tag
    _symbol = '\\dv'

    sort: Sort
    value: StrLit

    @classmethod
    def from_dict(cls: Type['DomVal'], dct: Mapping[str, Any]) -> 'DomVal':
        cls._check_tag(dct)
        return DomVal(
            sort=Sort.from_dict(dct['sort']),
            value=StrLit(dct['value']),  # TODO Haskell: StrLit.from_dict(...) would be nicer
        )

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unimplemented()

    @property
    def text(self) -> str:
        return self._symbol + ' { ' + self.sort.text + ' } ( ' + self.value.text + ' )'


# TODO
class MLSyntaxSugar(MLPattern, ABC):
    ...


@final
@dataclass(frozen=True)
class Attr(Kore):
    symbol: str
    params: Tuple[Union[StrLit, 'Attr'], ...]

    def __init__(self, symbol: str, params: Iterable[Union[StrLit, 'Attr']] = ()):
        check_symbol_id(symbol)
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'params', tuple(params))

    @classmethod
    @property
    def _tag(cls) -> str:
        # TODO
        return unsupported()

    @classmethod
    def from_dict(cls: Type['Attr'], dct: Mapping[str, Any]) -> 'Attr':
        # TODO
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unsupported()

    @property
    def text(self) -> str:
        return self.symbol + ' { } ' + _parend(param.text for param in self.params)


class WithAttrs(ABC):
    attrs: Tuple[Attr, ...]


class Sentence(Kore, WithAttrs, ABC):

    @classmethod
    def from_dict(cls: Type['Sentence'], dct: Mapping[str, Any]) -> 'Sentence':
        # TODO
        return unsupported()


@final
@dataclass(frozen=True)
class Import(Sentence):
    module_name: str
    attrs: Tuple[Attr, ...]

    def __init__(self, module_name: str, attrs: Iterable[Attr] = ()):
        check_id(module_name)
        object.__setattr__(self, 'module_name', module_name)
        object.__setattr__(self, 'attrs', tuple(attrs))

    @classmethod
    @property
    def _tag(cls) -> str:
        # TODO
        return unsupported()

    @classmethod
    def from_dict(cls: Type['Import'], dct: Mapping[str, Any]) -> 'Import':
        # TODO
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unsupported()

    @property
    def text(self) -> str:
        return ' '.join([
            'import',
            self.module_name,
            _brackd(attr.text for attr in self.attrs),
        ])


@final
@dataclass(frozen=True)
class SortDecl(Sentence):
    name: str
    vars: Tuple[SortVar, ...]
    attrs: Tuple[Attr, ...]
    hooked: bool

    def __init__(self, name: str, vars: Iterable[SortVar], attrs: Iterable[Attr] = (), *, hooked=False):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'attrs', tuple(attrs))
        object.__setattr__(self, 'hooked', hooked)

    @classmethod
    @property
    def _tag(cls) -> str:
        # TODO
        return unsupported()

    @classmethod
    def from_dict(cls: Type['SortDecl'], dct: Mapping[str, Any]) -> 'SortDecl':
        # TODO
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unsupported()

    @property
    def text(self) -> str:
        return ' '.join([
            'hooked-sort' if self.hooked else 'sort',
            self.name,
            _braced(var.text for var in self.vars),
            _brackd(attr.text for attr in self.attrs),
        ])


@final
@dataclass(frozen=True)
class Symbol(Kore):
    name: str
    vars: Tuple[SortVar, ...]

    def __init__(self, name: str, vars: Iterable[SortVar] = ()):
        check_symbol_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'vars', tuple(vars))

    @classmethod
    @property
    def _tag(cls) -> str:
        # TODO
        return unsupported()

    @classmethod
    def from_dict(cls: Type['Symbol'], dct: Mapping[str, Any]) -> 'Symbol':
        # TODO
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unsupported()

    @property
    def text(self) -> str:
        return self.name + ' ' + _braced(var.text for var in self.vars)


@final
@dataclass(frozen=True)
class SymbolDecl(Sentence):
    symbol: Symbol
    sort_params: Tuple[Sort, ...]
    sort: Sort
    attrs: Tuple[Attr, ...]
    hooked: bool

    def __init__(self, symbol: Symbol, sort_params: Iterable[Sort], sort: Sort, attrs: Iterable[Attr] = (), *, hooked=False):
        object.__setattr__(self, 'symbol', symbol)
        object.__setattr__(self, 'sort_params', tuple(sort_params))
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'attrs', tuple(attrs))
        object.__setattr__(self, 'hooked', hooked)

    @classmethod
    @property
    def _tag(cls) -> str:
        # TODO
        return unsupported()

    @classmethod
    def from_dict(cls: Type['SymbolDecl'], dct: Mapping[str, Any]) -> 'SymbolDecl':
        # TODO
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unsupported()

    @property
    def text(self) -> str:
        return ' '.join([
            'hooked-symbol' if self.hooked else 'symbol',
            self.symbol.text,
            _parend(sort.text for sort in self.sort_params),
            ':',
            self.sort.text,
            _brackd(attr.text for attr in self.attrs),
        ])


@final
@dataclass(frozen=True)
class AliasDecl(Sentence):
    alias: Symbol
    sort_params: Tuple[Sort, ...]
    sort: Sort
    left: Apply
    right: Pattern
    attrs: Tuple[Attr, ...]

    def __init__(
        self,
        alias: Symbol,
        sort_params: Iterable[Sort],
        sort: Sort,
        left: Apply,
        right: Pattern,
        attrs: Iterable[Attr] = (),
    ):
        object.__setattr__(self, 'alias', alias)
        object.__setattr__(self, 'sort_params', tuple(sort_params))
        object.__setattr__(self, 'sort', sort)
        object.__setattr__(self, 'left', left)
        object.__setattr__(self, 'right', right)
        object.__setattr__(self, 'attrs', tuple(attrs))

    @classmethod
    @property
    def _tag(cls) -> str:
        # TODO
        return unsupported()

    @classmethod
    def from_dict(cls: Type['AliasDecl'], dct: Mapping[str, Any]) -> 'AliasDecl':
        # TODO
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unsupported()

    @property
    def text(self) -> str:
        return ' '.join([
            'alias',
            self.alias.text,
            _parend(sort.text for sort in self.sort_params),
            ':',
            self.sort.text,
            'where',
            self.left.text,
            ':=',
            self.right.text,
            _brackd(attr.text for attr in self.attrs),
        ])


class AxiomLike(Sentence, ABC):
    label: ClassVar[str]  # TODO pull up to Sentence
    vars: Tuple[SortVar, ...]
    pattern: Pattern

    @classmethod
    def from_dict(cls: Type['AxiomLike'], dct: Mapping[str, Any]) -> 'AxiomLike':
        # TODO
        return unsupported()

    @property
    def text(self) -> str:
        return ' '.join([
            self.label,
            _braced(var.text for var in self.vars),
            self.pattern.text,
            _brackd(attr.text for attr in self.attrs),
        ])


@final
@dataclass(frozen=True)
class Axiom(AxiomLike):
    label = 'axiom'
    vars: Tuple[SortVar, ...]
    pattern: Pattern
    attrs: Tuple[Attr, ...]

    def __init__(self, vars: Iterable[SortVar], pattern: Pattern, attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'attrs', tuple(attrs))

    @classmethod
    @property
    def _tag(cls) -> str:
        # TODO
        return unsupported()

    @classmethod
    def from_dict(cls: Type['Axiom'], dct: Mapping[str, Any]) -> 'Axiom':
        # TODO
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unsupported()


@final
@dataclass(frozen=True)
class Claim(AxiomLike):
    label = 'claim'
    vars: Tuple[SortVar, ...]
    pattern: Pattern
    attrs: Tuple[Attr, ...]

    def __init__(self, vars: Iterable[SortVar], pattern: Pattern, attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'vars', tuple(vars))
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'attrs', tuple(attrs))

    @classmethod
    @property
    def _tag(cls) -> str:
        # TODO
        return unsupported()

    @classmethod
    def from_dict(cls: Type['Claim'], dct: Mapping[str, Any]) -> 'Claim':
        # TODO
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unsupported()


@final
@dataclass(frozen=True)
class Module(Kore, WithAttrs):
    name: str
    sentences: Tuple[Sentence, ...]
    attrs: Tuple[Attr, ...]

    def __init__(self, name: str, sentences: Iterable[Sentence] = (), attrs: Iterable[Attr] = ()):
        check_id(name)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sentences', tuple(sentences))
        object.__setattr__(self, 'attrs', tuple(attrs))

    @classmethod
    @property
    def _tag(cls) -> str:
        # TODO
        return unsupported()

    @classmethod
    def from_dict(cls: Type['Module'], dct: Mapping[str, Any]) -> 'Module':
        # TODO
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unsupported()

    @property
    def text(self) -> str:
        return '\n'.join(
            [f'module {self.name}'] +                                   # noqa: W504
            [f'    {sentence.text}' for sentence in self.sentences] +   # noqa: W504
            ['endmodule ' + _brackd(attr.text for attr in self.attrs)]  # noqa: W504
        )


@final
@dataclass(frozen=True)
class Definition(Kore, WithAttrs):
    modules: Tuple[Module, ...]
    attrs: Tuple[Attr, ...]

    def __init__(self, modules: Iterable[Module] = (), attrs: Iterable[Attr] = ()):
        object.__setattr__(self, 'modules', tuple(modules))
        object.__setattr__(self, 'attrs', tuple(attrs))

    @classmethod
    @property
    def _tag(cls) -> str:
        # TODO
        return unsupported()

    @classmethod
    def from_dict(cls: Type['Definition'], dct: Mapping[str, Any]) -> 'Definition':
        # TODO
        return unsupported()

    @property
    def dict(self) -> Dict[str, Any]:
        # TODO
        return unsupported()

    @property
    def text(self) -> str:
        return '\n\n'.join([
            _brackd(attr.text for attr in self.attrs),
        ] + [module.text for module in self.modules])
