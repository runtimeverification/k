from __future__ import annotations

from abc import ABC
from collections.abc import Sequence
from dataclasses import dataclass, field
from enum import Enum
from typing import TYPE_CHECKING, final, overload

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Any, Final


@dataclass(frozen=True)
class AST(ABC):
    source: Path | None = field(default=None, kw_only=True)
    location: tuple[int, int, int, int] | None = field(default=None, kw_only=True)


@final
@dataclass(frozen=True)
class Att(AST, Sequence[tuple[str, str]]):
    items: tuple[tuple[str, str], ...]

    def __init__(self, items: Iterable[tuple[str, str]] = ()):
        object.__setattr__(self, 'items', tuple(items))

    @overload
    def __getitem__(self, key: int) -> tuple[str, str]: ...

    @overload
    def __getitem__(self, key: slice) -> tuple[tuple[str, str], ...]: ...

    def __getitem__(self, key: Any) -> Any:
        return self.items[key]

    def __len__(self) -> int:
        return len(self.items)


EMPTY_ATT: Final = Att()


class Sentence(AST, ABC): ...


class SyntaxSentence(Sentence, ABC): ...


class Assoc(Enum):
    LEFT = 'left'
    RIGHT = 'right'
    NON_ASSOC = 'non-assoc'


@final
@dataclass(frozen=True)
class SortDecl(AST):
    name: str
    params: tuple[str, ...]
    args: tuple[str, ...]

    def __init__(self, name: str, params: Iterable[str] = (), args: Iterable[str] = ()):
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'params', tuple(params))
        object.__setattr__(self, 'args', tuple(args))


@final
@dataclass(frozen=True)
class Sort(AST):
    name: str
    args: tuple[int | str, ...]

    def __init__(self, name: str, args: Iterable[int | str] = ()):
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'args', tuple(args))


@final
@dataclass(frozen=True)
class SyntaxDecl(SyntaxSentence):
    decl: SortDecl
    att: Att = field(default=EMPTY_ATT)


@final
@dataclass(frozen=True)
class SyntaxDefn(SyntaxSentence):
    decl: SortDecl
    blocks: tuple[PriorityBlock, ...]

    def __init__(self, decl: SortDecl, blocks: Iterable[PriorityBlock] = ()):
        object.__setattr__(self, 'decl', decl)
        object.__setattr__(self, 'blocks', tuple(blocks))


@final
@dataclass(frozen=True)
class PriorityBlock(AST):
    productions: tuple[ProductionLike, ...]
    assoc: Assoc | None

    def __init__(self, productions: Iterable[ProductionLike], assoc: Assoc | None = None):
        object.__setattr__(self, 'productions', tuple(productions))
        object.__setattr__(self, 'assoc', assoc)


class ProductionLike(AST, ABC):
    att: Att


@final
@dataclass(frozen=True)
class Production(ProductionLike):
    items: tuple[ProductionItem, ...]
    att: Att = field(default=EMPTY_ATT)

    def __init__(self, items: Iterable[ProductionItem], att: Att = EMPTY_ATT):
        object.__setattr__(self, 'items', tuple(items))
        object.__setattr__(self, 'att', att)


class ProductionItem(AST, ABC): ...


@final
@dataclass(frozen=True)
class Terminal(ProductionItem):
    value: str


@final
@dataclass(frozen=True)
class NonTerminal(ProductionItem):
    sort: Sort
    name: str = field(default='')


@final
@dataclass(frozen=True)
class Lexical(ProductionItem):
    regex: str


@final
@dataclass(frozen=True)
class UserList(ProductionLike):
    sort: str
    sep: str
    non_empty: bool = field(default=False)
    att: Att = field(default=EMPTY_ATT)


@final
@dataclass(frozen=True)
class SyntaxSynonym(SyntaxSentence):
    new: SortDecl
    old: Sort
    att: Att = field(default=EMPTY_ATT)


@final
@dataclass(frozen=True)
class SyntaxPriority(SyntaxSentence):
    groups: tuple[tuple[str, ...], ...]

    def __init__(self, groups: Iterable[Iterable[str]]):
        object.__setattr__(self, 'groups', tuple(tuple(group) for group in groups))


@final
@dataclass(frozen=True)
class SyntaxAssoc(SyntaxSentence):
    assoc: Assoc
    klabels: tuple[str, ...]

    def __init__(self, assoc: Assoc, klabels: Iterable[str]):
        object.__setattr__(self, 'assoc', assoc)
        object.__setattr__(self, 'klabels', tuple(klabels))


@final
@dataclass(frozen=True)
class SyntaxLexical(SyntaxSentence):
    name: str
    regex: str


class StringSentence(Sentence, ABC):
    _prefix: str

    bubble: str
    label: str
    att: Att


@final
@dataclass(frozen=True)
class Rule(StringSentence):
    _prefix = 'rule'

    bubble: str
    label: str = field(default='')
    att: Att = field(default=EMPTY_ATT)


@final
@dataclass(frozen=True)
class Claim(StringSentence):
    _prefix = 'claim'

    bubble: str
    label: str = field(default='')
    att: Att = field(default=EMPTY_ATT)


@final
@dataclass(frozen=True)
class Config(StringSentence):
    _prefix = 'configuration'

    bubble: str
    label: str = field(default='')
    att: Att = field(default=EMPTY_ATT)


@final
@dataclass(frozen=True)
class Context(StringSentence):
    _prefix = 'context'

    bubble: str
    label: str = field(default='')
    att: Att = field(default=EMPTY_ATT)


@final
@dataclass(frozen=True)
class Alias(StringSentence):
    _prefix = 'context alias'

    bubble: str
    label: str = field(default='')
    att: Att = field(default=EMPTY_ATT)


@final
@dataclass(frozen=True)
class Import(AST):
    module_name: str
    public: bool = field(default=True, kw_only=True)


@final
@dataclass(frozen=True)
class Module(AST):
    name: str
    sentences: tuple[Sentence, ...]
    imports: tuple[Import, ...]
    att: Att

    def __init__(
        self,
        name: str,
        sentences: Iterable[Sentence] = (),
        imports: Iterable[Import] = (),
        att: Att = EMPTY_ATT,
        source: Path | None = None,
        location: tuple[int, int, int, int] | None = None,
    ):
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'sentences', tuple(sentences))
        object.__setattr__(self, 'imports', tuple(imports))
        object.__setattr__(self, 'att', att)
        object.__setattr__(self, 'source', source)
        object.__setattr__(self, 'location', location)


@final
@dataclass(frozen=True)
class Require(AST):
    path: str


@final
@dataclass(frozen=True)
class Definition(AST):
    modules: tuple[Module, ...]
    requires: tuple[Require, ...]

    def __init__(self, modules: Iterable[Module] = (), requires: Iterable[Require] = ()):
        object.__setattr__(self, 'modules', tuple(modules))
        object.__setattr__(self, 'requires', tuple(requires))
