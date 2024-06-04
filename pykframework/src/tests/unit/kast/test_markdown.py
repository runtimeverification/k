from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pykframework.kast.markdown import And, Atom, CodeBlock, Not, Or, SelectorParser, code_blocks, parse_tags, select_code_blocks

from ..utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from collections.abc import Collection, Iterator
    from pathlib import Path
    from typing import Final

    from pykframework.kast.markdown import Selector


CODE_BLOCKS_TEST_DIR: Final = TEST_DATA_DIR / 'markdown-code-blocks'
CODE_BLOCKS_TEST_FILES: Final = tuple(CODE_BLOCKS_TEST_DIR.glob('*.test'))
assert CODE_BLOCKS_TEST_FILES


@pytest.mark.parametrize(
    'test_file',
    CODE_BLOCKS_TEST_FILES,
    ids=[test_file.stem for test_file in CODE_BLOCKS_TEST_FILES],
)
def test_code_blocks(test_file: Path) -> None:
    # Given
    text, expected = _parse_code_blocks_test_data(test_file)

    # When
    actual = list(code_blocks(text))

    # Then
    assert actual == expected


def _parse_code_blocks_test_data(test_file: Path) -> tuple[str, list[CodeBlock]]:
    def _text(lines: Iterator[str]) -> str:
        text_lines: list[str] = []

        while True:
            line = next(lines)
            if line == '===':
                break
            text_lines.append(line)

        return '\n'.join(text_lines)

    def _blocks(lines: Iterator[str]) -> list[CodeBlock]:
        blocks: list[CodeBlock] = []

        la = next(lines, None)

        while la is not None:
            info = la
            code_lines: list[str] = []

            la = next(lines, None)
            while la is not None and la != '---':
                code_lines.append(la)
                la = next(lines, None)

            code = '\n'.join(code_lines)
            blocks.append(CodeBlock(info, code))

            if la:  # i.e. la == '---'
                la = next(lines, None)

        return blocks

    lines = test_file.read_text().splitlines()
    it = iter(lines)
    text = _text(it)
    blocks = _blocks(it)
    return text, blocks


PARSER_TEST_DATA: Final = (
    ('a', Atom('a')),
    (' a ', Atom('a')),
    ('(a)', Atom('a')),
    ('((a))', Atom('a')),
    ('foo', Atom('foo')),
    ('!a', Not(Atom('a'))),
    ('a & b', And((Atom('a'), Atom('b')))),
    ('a & b & c', And((Atom('a'), Atom('b'), Atom('c')))),
    ('a & (b & c)', And((Atom('a'), And((Atom('b'), Atom('c')))))),
    ('!(a & b)', Not(And((Atom('a'), Atom('b'))))),
    ('(a & b) & c', And((And((Atom('a'), Atom('b'))), Atom('c')))),
    ('a & !b & !c', And((Atom('a'), Not(Atom('b')), Not(Atom('c'))))),
    ('a | b', Or((Atom('a'), Atom('b')))),
    ('a | b | c', Or((Atom('a'), Atom('b'), Atom('c')))),
    ('!a | !b | c', Or((Not(Atom('a')), Not(Atom('b')), Atom('c')))),
    ('a | b & !c', Or((Atom('a'), And((Atom('b'), Not(Atom('c'))))))),
    ('!(a | b)', Not(Or((Atom('a'), Atom('b'))))),
    ('(a | b) & !c', And((Or((Atom('a'), Atom('b'))), Not(Atom('c'))))),
    ('!a & b | c', Or((And((Not(Atom('a')), Atom('b'))), Atom('c')))),
    ('!a & (b | c)', And((Not(Atom('a')), Or((Atom('b'), Atom('c')))))),
)


@pytest.mark.parametrize('text,expected', PARSER_TEST_DATA, ids=[text for text, _ in PARSER_TEST_DATA])
def test_selector_parser(text: str, expected: Selector) -> None:
    # Given
    parser = SelectorParser(text)

    # When
    actual = parser.parse()

    # Then
    assert actual == expected


EVAL_TEST_DATA: Final[tuple[tuple[str, list[str], bool], ...]] = (
    ('a', [], False),
    ('a', ['a'], True),
    ('a', ['a', 'b'], True),
    ('a', ['b'], False),
    ('!a', [], True),
    ('!a', ['a'], False),
    ('!a', ['a', 'b'], False),
    ('!a', ['b'], True),
    ('a & b', [], False),
    ('a & b', ['a'], False),
    ('a & b', ['b'], False),
    ('a & b', ['a', 'b'], True),
    ('a | b', [], False),
    ('a | b', ['a'], True),
    ('a | b', ['b'], True),
    ('a | b', ['a', 'b'], True),
    ('!a | b & c', [], True),
    ('!a | b & c', ['a'], False),
    ('!a | b & c', ['b, c'], True),
    ('a & (!b | c)', [], False),
    ('a & (!b | c)', ['a'], True),
    ('a & (!b | c)', ['a', 'b'], False),
    ('a & (!b | c)', ['a', 'b', 'c'], True),
)


def _eval_id(text: str, atoms: Collection[str], expected: bool) -> str:
    models = '|==' if expected else '|=/='
    return '{' + ','.join(atoms) + '} ' + f'{models} {text}'


@pytest.mark.parametrize(
    'text,atoms,expected', EVAL_TEST_DATA, ids=[_eval_id(*test_data) for test_data in EVAL_TEST_DATA]
)
def test_selector_eval(text: str, atoms: Collection[str], expected: bool) -> None:
    # Given
    parser = SelectorParser(text)
    selector = parser.parse()

    # When
    actual = selector.eval(atoms)

    # Then
    assert actual == expected


PARSE_TAGS_TEST_DATA: Final[tuple[tuple[str, set[str]], ...]] = (
    ('', set()),
    ('k', {'k'}),
    ('{.foo .bar .baz}', {'foo', 'bar', 'baz'}),
)


@pytest.mark.parametrize('text,expected', PARSE_TAGS_TEST_DATA, ids=[text for text, _ in PARSE_TAGS_TEST_DATA])
def test_parse_tags(text: str, expected: set[str]) -> None:
    # When
    actual = parse_tags(text)

    # Then
    assert actual == expected


SELECT_TEST_DIR: Final = TEST_DATA_DIR / 'markdown-select'
SELECT_TEST_FILES: Final = tuple(SELECT_TEST_DIR.glob('*.test'))
assert SELECT_TEST_FILES


@pytest.mark.parametrize(
    'test_file',
    SELECT_TEST_FILES,
    ids=[test_file.stem for test_file in SELECT_TEST_FILES],
)
def test_select_code_blocks(test_file: Path) -> None:
    # Given
    selector, text, expected = _parse_select_test_data(test_file)

    # When
    actual = select_code_blocks(text, selector)

    # Then
    assert actual == expected


def _parse_select_test_data(test_file: Path) -> tuple[str | None, str, str]:
    lines = test_file.read_text().splitlines()
    it = iter(lines)

    selector = next(it) or None

    text_lines: list[str] = []
    while True:
        text_line = next(it)
        if text_line == '===':
            break
        text_lines.append(text_line)
    text = '\n'.join(text_lines)

    expected_lines: list[str] = []
    while True:
        expected_line = next(it, None)
        if expected_line is None:
            break
        expected_lines.append(expected_line)
    expected = '\n'.join(expected_lines)

    return selector, text, expected
