from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from enum import Enum
from typing import TYPE_CHECKING, final

if TYPE_CHECKING:
    from collections.abc import Iterable


def indent(text: str, n: int) -> str:
    indent = n * ' '
    res = []
    for line in text.splitlines():
        res.append(f'{indent}{line}' if line else '')
    return '\n'.join(res)


@final
@dataclass(frozen=True)
class Module:
    commands: tuple[Command, ...]

    def __init__(self, commands: Iterable[Command] | None = None):
        commands = tuple(commands) if commands is not None else ()
        object.__setattr__(self, 'commands', commands)

    def __str__(self) -> str:
        return '\n\n'.join(str(command) for command in self.commands)


class Command(ABC): ...


class Mutual(Command):
    commands: tuple[Command, ...]

    def __init__(self, commands: Iterable[Command] | None = None):
        commands = tuple(commands) if commands is not None else ()
        object.__setattr__(self, 'commands', commands)

    def __str__(self) -> str:
        commands = '\n\n'.join(indent(str(command), 2) for command in self.commands)
        return f'mutual\n{commands}\nend'


class Declaration(Command, ABC):
    modifiers: Modifiers | None


@final
@dataclass
class Abbrev(Declaration):
    ident: DeclId
    val: Term  # declVal
    signature: Signature | None
    modifiers: Modifiers | None

    def __init__(
        self,
        ident: str | DeclId,
        val: Term,
        signature: Signature | None = None,
        modifiers: Modifiers | None = None,
    ):
        ident = DeclId(ident) if isinstance(ident, str) else ident
        object.__setattr__(self, 'ident', ident)
        object.__setattr__(self, 'val', val)
        object.__setattr__(self, 'signature', signature)
        object.__setattr__(self, 'modifiers', modifiers)

    def __str__(self) -> str:
        modifiers = f'{self.modifiers} ' if self.modifiers else ''
        signature = f' {self.signature}' if self.signature else ''
        return f'{modifiers}abbrev {self.ident}{signature} := {self.val}'


@final
@dataclass(frozen=True)
class Inductive(Declaration):
    ident: DeclId
    signature: Signature | None
    ctors: tuple[Ctor, ...]
    deriving: tuple[str, ...]
    modifiers: Modifiers | None

    def __init__(
        self,
        ident: str | DeclId,
        signature: Signature | None = None,
        ctors: Iterable[Ctor] | None = None,
        deriving: Iterable[str] | None = None,
        modifiers: Modifiers | None = None,
    ):
        ident = DeclId(ident) if isinstance(ident, str) else ident
        ctors = tuple(ctors) if ctors is not None else ()
        deriving = tuple(deriving) if deriving is not None else ()
        object.__setattr__(self, 'ident', ident)
        object.__setattr__(self, 'signature', signature)
        object.__setattr__(self, 'ctors', ctors)
        object.__setattr__(self, 'deriving', deriving)
        object.__setattr__(self, 'modifiers', modifiers)

    def __str__(self) -> str:
        modifiers = f'{self.modifiers} ' if self.modifiers else ''
        signature = f' {self.signature}' if self.signature else ''
        where = ' where' if self.ctors else ''
        deriving = ', '.join(self.deriving)

        lines = []
        lines.append(f'{modifiers}inductive {self.ident}{signature}{where}')
        for ctor in self.ctors:
            lines.append(f'  | {ctor}')
        if deriving:
            lines.append(f'  deriving {deriving}')
        return '\n'.join(lines)


@final
@dataclass(frozen=True)
class DeclId:
    val: str
    uvars: tuple[str, ...]

    def __init__(self, val: str, uvars: Iterable[str] | None = None):
        uvars = tuple(uvars) if uvars is not None else ()
        object.__setattr__(self, 'val', val)
        object.__setattr__(self, 'uvars', uvars)

    def __str__(self) -> str:
        uvars = ', '.join(self.uvars)
        uvars = '.{' + uvars + '}' if uvars else ''
        return f'{self.val}{uvars}'


@final
@dataclass(frozen=True)
class Ctor:
    ident: str
    signature: Signature | None = None
    modifiers: Modifiers | None = None

    def __str__(self) -> str:
        modifiers = f'{self.modifiers} ' if self.modifiers else ''
        signature = f' {self.signature}' if self.signature else ''
        return f'{modifiers}{self.ident}{signature}'


@final
@dataclass(frozen=True)
class Signature:
    binders: tuple[Binder, ...]
    ty: Term | None

    def __init__(self, binders: Iterable[Binder] | None = None, ty: Term | None = None):
        binders = tuple(binders) if binders is not None else ()
        object.__setattr__(self, 'binders', binders)
        object.__setattr__(self, 'ty', ty)

    def __str__(self) -> str:
        binders = ' '.join(str(binder) for binder in self.binders)
        sep = ' ' if self.binders else ''
        ty = f'{sep}: {self.ty}' if self.ty else ''
        return f'{binders}{ty}'


class Binder(ABC): ...


class BracketBinder(Binder, ABC): ...


@final
@dataclass(frozen=True)
class ExplBinder(BracketBinder):
    idents: tuple[str, ...]
    ty: Term | None

    def __init__(self, idents: Iterable[str], ty: Term | None = None):
        object.__setattr__(self, 'idents', tuple(idents))
        object.__setattr__(self, 'ty', ty)

    def __str__(self) -> str:
        idents = ' '.join(self.idents)
        ty = '' if self.ty is None else f' : {self.ty}'
        return f'({idents}{ty})'


@final
@dataclass(frozen=True)
class ImplBinder(BracketBinder):
    idents: tuple[str, ...]
    ty: Term | None
    strict: bool

    def __init__(self, idents: Iterable[str], ty: Term | None = None, *, strict: bool | None = None):
        object.__setattr__(self, 'idents', tuple(idents))
        object.__setattr__(self, 'ty', ty)
        object.__setattr__(self, 'strict', bool(strict))

    def __str__(self) -> str:
        ldelim, rdelim = ['⦃', '⦄'] if self.strict else ['{', '}']
        idents = ' '.join(self.idents)
        ty = '' if self.ty is None else f' : {self.ty}'
        return f'{ldelim}{idents}{ty}{rdelim}'


@final
@dataclass(frozen=True)
class InstBinder(BracketBinder):
    ty: Term
    ident: str | None

    def __init__(self, ty: Term, ident: str | None = None):
        object.__setattr__(self, 'ty', ty)
        object.__setattr__(self, 'ident', ident)

    def __str__(self) -> str:
        ident = f'{self.ident} : ' if self.ident else ''
        return f'[{ident}{self.ty}]'


@final
@dataclass(frozen=True)
class Term:
    term: str  # TODO: refine

    def __str__(self) -> str:
        return self.term


@final
@dataclass(frozen=True)
class Modifiers:
    attrs: tuple[Attr, ...]
    visibility: Visibility | None
    noncomputable: bool
    unsafe: bool
    totality: Totality | None

    def __init__(
        self,
        *,
        attrs: Iterable[str | Attr] | None = None,
        visibility: str | Visibility | None = None,
        noncomputable: bool | None = None,
        unsafe: bool | None = None,
        totality: str | Totality | None = None,
    ):
        attrs = tuple(Attr(attr) if isinstance(attr, str) else attr for attr in attrs) if attrs is not None else ()
        visibility = Visibility(visibility) if isinstance(visibility, str) else visibility
        noncomputable = bool(noncomputable)
        unsafe = bool(unsafe)
        totality = Totality(totality) if isinstance(totality, str) else totality
        object.__setattr__(self, 'attrs', attrs)
        object.__setattr__(self, 'visibility', visibility)
        object.__setattr__(self, 'noncomputable', noncomputable)
        object.__setattr__(self, 'unsafe', unsafe)
        object.__setattr__(self, 'totality', totality)

    def __str__(self) -> str:
        chunks = []
        if self.attrs:
            attrs = ', '.join(str(attr) for attr in self.attrs)
            chunks.append(f'@[{attrs}]')
        if self.visibility:
            chunks.append(self.visibility.value)
        if self.noncomputable:
            chunks.append('noncomputable')
        if self.unsafe:
            chunks.append('unsafe')
        if self.totality:
            chunks.append(self.totality.value)
        return ' '.join(chunks)


@final
@dataclass(frozen=True)
class Attr:
    attr: str
    kind: AttrKind | None

    def __init__(self, attr: str, kind: AttrKind | None = None):
        object.__setattr__(self, 'attr', attr)
        object.__setattr__(self, 'kind', kind)

    def __str__(self) -> str:
        if self.kind:
            return f'{self.kind.value} {self.attr}'
        return self.attr


class AttrKind(Enum):
    SCOPED = 'scoped'
    LOCAL = 'local'


class Visibility(Enum):
    PRIVATE = 'private'
    PROTECTED = 'protected'


class Totality(Enum):
    PARTIAL = 'partial'
    NONREC = 'nonrec'
