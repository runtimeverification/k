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
    imports: tuple[str, ...]
    commands: tuple[Command, ...]

    def __init__(
        self,
        imports: Iterable[str] | None = None,
        commands: Iterable[Command] | None = None,
    ):
        imports = tuple(imports) if imports is not None else ()
        commands = tuple(commands) if commands is not None else ()
        object.__setattr__(self, 'imports', imports)
        object.__setattr__(self, 'commands', commands)

    def __str__(self) -> str:
        imports = '\n'.join(f'import {importt}' for importt in self.imports)
        commands = '\n\n'.join(str(command) for command in self.commands)
        return '\n\n'.join(section for section in [imports, commands] if section)


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
class Axiom(Declaration):
    ident: DeclId
    signature: Signature
    modifiers: Modifiers | None

    def __init__(self, ident: str | DeclId, signature: Signature, modifiers: Modifiers | None = None):
        ident = DeclId(ident) if isinstance(ident, str) else ident
        object.__setattr__(self, 'ident', ident)
        object.__setattr__(self, 'signature', signature)
        object.__setattr__(self, 'modifiers', modifiers)

    def __str__(self) -> str:
        modifiers = f'{self.modifiers} ' if self.modifiers else ''
        return f'{modifiers}axiom {self.ident} {self.signature}'


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
class Instance(Declaration):
    signature: Signature
    val: DeclVal
    attr_kind: AttrKind | None
    priority: int | None
    ident: DeclId | None
    modifiers: Modifiers | None

    def __init__(
        self,
        signature: Signature,
        val: DeclVal,
        attr_kind: AttrKind | None = None,
        priority: int | None = None,
        ident: str | DeclId | None = None,
        modifiers: Modifiers | None = None,
    ):
        if priority and priority < 0:
            raise ValueError('Priority must be non-negative')
        if not signature.ty:
            # TODO refine type to avoid this check
            raise ValueError('Missing type from signature')
        ident = DeclId(ident) if isinstance(ident, str) else ident
        object.__setattr__(self, 'signature', signature)
        object.__setattr__(self, 'val', val)
        object.__setattr__(self, 'attr_kind', attr_kind)
        object.__setattr__(self, 'priority', priority)
        object.__setattr__(self, 'ident', ident)
        object.__setattr__(self, 'modifiers', modifiers)

    def __str__(self) -> str:
        modifiers = f'{self.modifiers} ' if self.modifiers else ''
        attr_kind = f'{self.attr_kind.value} ' if self.attr_kind else ''
        priority = f' (priority := {self.priority})' if self.priority is not None else ''
        ident = f' {self.ident}' if self.ident else ''
        signature = f' {self.signature}' if self.signature else ''

        decl = f'{modifiers}{attr_kind}instance{priority}{ident}{signature}'

        match self.val:
            case SimpleVal():
                return f'{decl} := {self.val}'
            case StructVal(fields):
                lines = []
                lines.append(f'{decl} where')
                lines.extend(indent(str(field), 2) for field in fields)
                return '\n'.join(lines)
            case _:
                raise AssertionError()


class Definition(Declaration):
    ident: DeclId
    val: DeclVal
    signature: Signature | None
    deriving: tuple[str, ...]
    modifiers: Modifiers | None

    def __init__(
        self,
        ident: str | DeclId,
        val: DeclVal,
        signature: Signature | None = None,
        deriving: Iterable[str] | None = None,
        modifiers: Modifiers | None = None,
    ):
        ident = DeclId(ident) if isinstance(ident, str) else ident
        deriving = tuple(deriving) if deriving is not None else ()
        object.__setattr__(self, 'ident', ident)
        object.__setattr__(self, 'val', val)
        object.__setattr__(self, 'signature', signature)
        object.__setattr__(self, 'deriving', deriving)
        object.__setattr__(self, 'modifiers', modifiers)

    def __str__(self) -> str:
        modifiers = f'{self.modifiers} ' if self.modifiers else ''
        signature = f' {self.signature}' if self.signature else ''

        decl = f'{modifiers}def {self.ident}{signature}'

        lines = []
        match self.val:
            case SimpleVal():
                lines.append(f'{decl} := {self.val}')
            case StructVal(fields):
                lines.append(f'{decl} where')
                lines.extend(indent(str(field), 2) for field in fields)
            case AltsVal(alts):
                lines.append(f'{decl}')
                lines.extend(indent(str(alt), 2) for alt in alts)

        if self.deriving:
            deriving = ', '.join(self.deriving)
            lines.append(f'  deriving {deriving}')

        return '\n'.join(lines)


class DeclVal(ABC): ...


@final
@dataclass(frozen=True)
class SimpleVal(DeclVal):
    term: Term

    def __str__(self) -> str:
        return str(self.term)


@final
@dataclass(frozen=True)
class StructVal(DeclVal):
    fields: tuple[InstField, ...]

    def __init__(self, fields: Iterable[InstField]):
        object.__setattr__(self, 'fields', tuple(fields))

    def __str__(self) -> str:
        return indent('\n'.join(str(field) for field in self.fields), 2)


@final
@dataclass(frozen=True)
class AltsVal(DeclVal):
    alts: tuple[Alt, ...]

    def __init__(self, alts: Iterable[Alt]):
        object.__setattr__(self, 'alts', tuple(alts))

    def __str__(self) -> str:
        return indent('\n'.join(str(alt) for alt in self.alts), 2)


@final
@dataclass(frozen=True)
class InstField:
    lval: str
    val: FieldVal
    signature: Signature | None

    def __init__(self, lval: str, val: FieldVal, signature: Signature | None = None):
        object.__setattr__(self, 'lval', lval)
        object.__setattr__(self, 'val', val)
        object.__setattr__(self, 'signature', signature)

    def __str__(self) -> str:
        signature = f' {self.signature}' if self.signature else ''
        decl = f'{self.lval}{signature}'
        match self.val:
            case SimpleFieldVal():
                return f'{decl} := {self.val}'
            case AltsFieldVal(alts):
                lines = []
                lines.append(f'{decl}')
                lines.extend(indent(str(alt), 2) for alt in alts)
                return '\n'.join(lines)
            case _:
                raise AssertionError()


class FieldVal(ABC): ...


@final
@dataclass(frozen=True)
class SimpleFieldVal(FieldVal):
    term: Term

    def __str__(self) -> str:
        return str(self.term)


@final
@dataclass(frozen=True)
class AltsFieldVal(FieldVal):
    alts: tuple[Alt, ...]

    def __init__(self, alts: Iterable[Alt]):
        object.__setattr__(self, 'alts', tuple(alts))

    def __str__(self) -> str:
        return indent('\n'.join(str(alt) for alt in self.alts), 2)


@final
@dataclass(frozen=True)
class Alt:
    patterns: tuple[Term, ...]
    rhs: Term

    def __init__(self, patterns: Iterable[Term], rhs: Term):
        object.__setattr__(self, 'patterns', tuple(patterns))
        object.__setattr__(self, 'rhs', rhs)

    def __str__(self) -> str:
        patterns = ', '.join(str(pattern) for pattern in self.patterns)
        return f'| {patterns} => {self.rhs}'


@final
@dataclass(frozen=True)
class Structure(Declaration):
    ident: DeclId
    signature: Signature | None
    extends: tuple[Term, ...]
    ctor: StructCtor | None
    deriving: tuple[str, ...]
    modifiers: Modifiers | None

    def __init__(
        self,
        ident: str | DeclId,
        signature: Signature | None = None,
        extends: Iterable[Term] | None = None,
        ctor: StructCtor | None = None,
        deriving: Iterable[str] | None = None,
        modifiers: Modifiers | None = None,
    ):
        ident = DeclId(ident) if isinstance(ident, str) else ident
        extends = tuple(extends) if extends is not None else ()
        deriving = tuple(deriving) if deriving is not None else ()
        object.__setattr__(self, 'ident', ident)
        object.__setattr__(self, 'signature', signature)
        object.__setattr__(self, 'extends', extends)
        object.__setattr__(self, 'ctor', ctor)
        object.__setattr__(self, 'deriving', deriving)
        object.__setattr__(self, 'modifiers', modifiers)

    def __str__(self) -> str:
        lines = []

        modifiers = f'{self.modifiers} ' if self.modifiers else ''
        binders = (
            ' '.join(str(binder) for binder in self.signature.binders)
            if self.signature and self.signature.binders
            else ''
        )
        binders = f' {binders}' if binders else ''
        extends = ', '.join(str(extend) for extend in self.extends)
        extends = f' extends {extends}' if extends else ''
        ty = f' : {self.signature.ty}' if self.signature and self.signature.ty else ''
        where = ' where' if self.ctor else ''
        lines.append(f'{modifiers}structure {self.ident}{binders}{extends}{ty}{where}')

        if self.ctor:
            lines.extend(f'  {line}' for line in str(self.ctor).splitlines())

        if self.deriving:
            deriving = ', '.join(self.deriving)
            lines.append(f'  deriving {deriving}')

        return '\n'.join(lines)


@final
@dataclass(frozen=True)
class StructCtor:
    fields: tuple[Binder, ...]  # TODO implement StructField
    ident: StructIdent | None

    def __init__(
        self,
        fields: Iterable[Binder],
        ident: str | StructIdent | None = None,
    ):
        fields = tuple(fields)
        ident = StructIdent(ident) if isinstance(ident, str) else ident
        object.__setattr__(self, 'fields', fields)
        object.__setattr__(self, 'ident', ident)

    def __str__(self) -> str:
        lines = []
        if self.ident:
            lines.append(f'{self.ident} ::')
        for field in self.fields:
            if isinstance(field, ExplBinder) and len(field.idents) == 1:
                (ident,) = field.idents
                ty = '' if field.ty is None else f' : {field.ty}'
                lines.append(f'{ident}{ty}')
            else:
                lines.append(str(field))
        return '\n'.join(lines)


@final
@dataclass(frozen=True)
class StructIdent:
    ident: str
    modifiers: Modifiers | None = None

    def __str__(self) -> str:
        modifiers = f'{self.modifiers} ' if self.modifiers else ''
        return f'{modifiers}{ self.ident}'


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
