from __future__ import annotations

import re
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import TYPE_CHECKING, NamedTuple, final

if TYPE_CHECKING:
    from collections.abc import Container, Iterable, Iterator
    from typing import Final


def select_code_blocks(text: str, selector: str | None = None) -> str:
    _selector = SelectorParser(selector).parse() if selector else None

    def selected(code_block: CodeBlock) -> bool:
        if _selector is None:
            return True

        tags = parse_tags(code_block.info)
        return _selector.eval(tags)

    # TODO: Preserve line numbers from input text
    return '\n'.join(code_block.code for code_block in code_blocks(text) if selected(code_block))


class CodeBlock(NamedTuple):
    info: str
    code: str


_CODE_BLOCK_PATTERN: Final = re.compile(
    r'(^|(?<=\n)) {0,3}(?P<fence>```+)(?!`)(?P<info>.*)\n(?P<code>(.*\n)*?) {0,3}(?P=fence)`*'
)


def code_blocks(text: str) -> Iterator[CodeBlock]:
    return (CodeBlock(match['info'], match['code'].rstrip()) for match in _CODE_BLOCK_PATTERN.finditer(text))


def parse_tags(text: str) -> set[str]:
    def check_tag(tag: str) -> None:
        if not (tag and all(c.isalnum() or c in '_-' for c in tag)):
            raise ValueError(f'Invalid tag: {tag!r}')

    if not text:
        return set()

    if text[0] != '{':
        check_tag(text)
        return {text}

    if text[-1] != '}':
        raise ValueError("Expected '}', found: {text[-1]!r}")

    res: set[str] = set()
    tags = text[1:-1].split()
    for tag in tags:
        if tag[0] != '.':
            raise ValueError("Expected '.', found: {tag[0]!r}")
        check_tag(tag[1:])
        res.add(tag[1:])

    return res


# ----------------------
# Selector mini-language
# ----------------------


class Selector(ABC):
    @abstractmethod
    def eval(self, atoms: Container[str]) -> bool: ...


@final
@dataclass(frozen=True)
class Atom(Selector):
    name: str

    def eval(self, atoms: Container[str]) -> bool:
        return self.name in atoms


@final
@dataclass(frozen=True)
class Not(Selector):
    op: Selector

    def eval(self, atoms: Container[str]) -> bool:
        return not self.op.eval(atoms)


@final
@dataclass(frozen=True)
class And(Selector):
    ops: tuple[Selector, ...]

    def eval(self, atoms: Container[str]) -> bool:
        return all(op.eval(atoms) for op in self.ops)


@final
@dataclass(frozen=True)
class Or(Selector):
    ops: tuple[Selector, ...]

    def eval(self, atoms: Container[str]) -> bool:
        return any(op.eval(atoms) for op in self.ops)


_SPECIAL = tuple('!&|()')


def selector_lexer(it: Iterable[str]) -> Iterator[str]:
    it = iter(it)
    la = next(it, '')
    while True:
        while la.isspace():
            la = next(it, '')

        if not la:
            yield ''
            return

        if la in _SPECIAL:
            yield la
            la = next(it, '')
            continue

        buf: list[str] = []
        while la.isalnum() or la == '_':
            buf.append(la)
            la = next(it, '')

        if not buf:
            raise ValueError(f'Unexpected character: {la!r}')

        yield ''.join(buf)


class SelectorParser:
    _la: str
    _it: Iterator[str]

    def __init__(self, selector: str):
        self._it = selector_lexer(selector)
        self._consume()

    def _consume(self) -> None:
        self._la = next(self._it, '')

    def _match(self, token: str) -> None:
        if self._la != token:
            raise ValueError('Unexpected token: {token}')
        self._consume()

    def parse(self) -> Selector:
        res = self._or()
        if self._la:
            raise ValueError(f'Expected EOF, found: {self._la}')
        return res

    def _or(self) -> Selector:
        ops = [self._and()]
        while self._la == '|':
            self._consume()
            ops.append(self._and())
        if len(ops) > 1:
            return Or(tuple(ops))
        return ops[0]

    def _and(self) -> Selector:
        ops = [self._lit()]
        while self._la == '&':
            self._consume()
            ops.append(self._lit())
        if len(ops) > 1:
            return And(tuple(ops))
        return ops[0]

    def _lit(self) -> Selector:
        if not self._la:
            raise ValueError('Unexpected EOF')

        if self._la == '(':
            self._consume()
            expr = self._or()
            self._match(')')
            return expr

        if self._la == '!':
            self._consume()
            lit = self._lit()
            return Not(lit)

        if len(self._la) > 1 or self._la.isalnum() or self._la == '-':
            atom = self._la
            self._consume()
            return Atom(atom)

        raise ValueError(f'Unexpected token: {self._la}')
