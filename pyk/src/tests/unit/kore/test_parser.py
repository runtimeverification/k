from __future__ import annotations

import json
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.kore.parser import KoreParser
from pyk.kore.syntax import And, App, Kore, Or, Pattern, SortVar, kore_term

if TYPE_CHECKING:
    from collections.abc import Mapping
    from typing import Any, Final

TEST_DATA_DIR: Final = Path(__file__).parent / 'test-data'

DEFINITION_PASS_KORE_FILES: Final = tuple((TEST_DATA_DIR / 'definitions/pass').iterdir())
DEFINITION_FAIL_KORE_FILES: Final = tuple(
    test_file for test_file in (TEST_DATA_DIR / 'definitions/fail').iterdir() if test_file.suffix == '.kore'
)

PATTERN_FILES: Final = tuple((TEST_DATA_DIR / 'patterns').iterdir())

JSON_FILES: Final = tuple((TEST_DATA_DIR / 'json').iterdir())
JSON_TEST_DATA: Final = tuple(
    (json_file, i, dct) for json_file in JSON_FILES for i, dct in enumerate(json.loads(json_file.read_text()))
)


@pytest.mark.parametrize(
    'kore_file', DEFINITION_PASS_KORE_FILES, ids=lambda path: path.name
)  # mypy complains on Path.name.fget
def test_parse_definition_pass(kore_file: Path) -> None:
    # Given
    text = kore_file.read_text()

    # When
    parser1 = KoreParser(text)
    definition1 = parser1.definition()
    parser2 = KoreParser(definition1.text)
    definition2 = parser2.definition()

    # Then
    assert parser1.eof
    assert parser2.eof
    assert definition1 == definition2


@pytest.mark.parametrize('kore_file', DEFINITION_FAIL_KORE_FILES, ids=lambda path: path.name)
def test_parse_definition_fail(kore_file: Path) -> None:
    # Given
    text = kore_file.read_text()
    parser = KoreParser(text)

    # Then
    with pytest.raises(ValueError):
        # When
        parser.definition()


@pytest.mark.parametrize('kore_file', PATTERN_FILES, ids=lambda path: path.name)
def test_parse_pattern(kore_file: Path) -> None:
    # Given
    text = kore_file.read_text()

    # When
    parser1 = KoreParser(text)
    pattern1 = parser1.pattern()
    parser2 = KoreParser(pattern1.text)
    pattern2 = parser2.pattern()
    pattern3 = Pattern.from_dict(pattern1.dict)

    # Then
    assert parser1.eof
    assert parser2.eof
    assert pattern1 == pattern2
    assert pattern1 == pattern3


@pytest.mark.parametrize(
    'json_file,i,dct', JSON_TEST_DATA, ids=[f'{json_file.name}-{i}' for json_file, i, _ in JSON_TEST_DATA]
)
def test_parse_json(json_file: Path, i: int, dct: Mapping[str, Any]) -> None:
    # When
    kore1: Kore = kore_term(dct)  # TODO type hint should be unnecessary
    parser = KoreParser(kore1.text)
    kore2 = parser.pattern()
    kore3 = Kore.from_json(kore1.json)

    # Then
    assert parser.eof
    assert kore1 == kore2
    assert kore1 == kore3


x, y, z = (App(name) for name in ['x', 'y', 'z'])
MULTI_OR_TEST_DATA: Final[tuple[tuple[str, str, list[Pattern]], ...]] = (
    ('nullary', r'\left-assoc{}(\or{S}())', []),
    ('unary', r'\left-assoc{}(\or{S}(x{}()))', [x]),
    ('binary', r'\left-assoc{}(\or{S}(x{}(), y{}()))', [x, y]),
    ('multiary', r'\left-assoc{}(\or{S}(x{}(), y{}(), z{}()))', [x, y, z]),
)


@pytest.mark.parametrize(
    'test_id,text,expected',
    MULTI_OR_TEST_DATA,
    ids=[test_id for test_id, *_ in MULTI_OR_TEST_DATA],
)
def test_multi_or(test_id: str, text: str, expected: list[Pattern]) -> None:
    # Given
    parser = KoreParser(text)

    # When
    actual = parser.multi_or()

    # Then
    assert parser.eof
    assert actual == expected


S = SortVar('S')
a, b, c, d = (App(name) for name in ['a', 'b', 'c', 'd'])
MULTIARY_TEST_DATA: Final = (
    ('binary-and', r'\and{S}(a{}(), b{}())', And(S, a, b)),
    ('ternary-and', r'\and{S}(a{}(), b{}(), c{}())', And(S, And(S, a, b), c)),
    ('quaternary-and', r'\and{S}(a{}(), b{}(), c{}(), d{}())', And(S, And(S, And(S, a, b), c), d)),
    ('binary-or', r'\or{S}(a{}(), b{}())', Or(S, a, b)),
    ('ternary-or', r'\or{S}(a{}(), b{}(), c{}())', Or(S, Or(S, a, b), c)),
    ('quaternary-or', r'\or{S}(a{}(), b{}(), c{}(), d{}())', Or(S, Or(S, Or(S, a, b), c), d)),
)


@pytest.mark.parametrize(
    'test_id,text,expected',
    MULTIARY_TEST_DATA,
    ids=[test_id for test_id, *_ in MULTIARY_TEST_DATA],
)
def test_multiary(test_id: str, text: str, expected: list[Pattern]) -> None:
    # Given
    parser = KoreParser(text)

    # When
    actual = parser.pattern()

    # Then
    assert parser.eof
    assert actual == expected
