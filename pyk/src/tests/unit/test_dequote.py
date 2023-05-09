from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

if TYPE_CHECKING:
    from typing import Final

from pyk.dequote import bytes_decode, bytes_encode, dequote_bytes, dequote_string, enquote_bytes, enquote_string

BASE_TEST_DATA: Final = (
    # enquoted, dequoted, encoded
    ('', '', b''),
    (' ', ' ', b' '),
    ('1', '1', b'1'),
    ('012', '012', b'012'),
    ('a', 'a', b'a'),
    ('abc', 'abc', b'abc'),
    ("'", "'", b"'"),
    (r'\\ ', r'\ ', rb'\ '),
    (r'\\1', r'\1', rb'\1'),
    (r'\\a', r'\a', rb'\a'),
    ('\\\\', '\\', b'\\'),
    (r'\"', '"', b'"'),
    (r'\t', '\t', b'\t'),
    (r'\n', '\n', b'\n'),
    (r'\r', '\r', b'\r'),
    (r'\f', '\f', b'\f'),
    (r'Hello World!\n', 'Hello World!\n', b'Hello World!\n'),
    (r'\r\n', '\r\n', b'\r\n'),
    ('$', '$', b'$'),
    (r'\x00', '\x00', b'\x00'),
    (r'\x80', '\x80', b'\x80'),
    (r'\x00\x80', '\x00\x80', b'\x00\x80'),
)


BYTES_ENCODE_TEST_DATA = tuple((dequoted, encoded) for _, dequoted, encoded in BASE_TEST_DATA)


@pytest.mark.parametrize(
    'dequoted, expected',
    BYTES_ENCODE_TEST_DATA,
    ids=[dequoted for dequoted, *_ in BYTES_ENCODE_TEST_DATA],
)
def test_encode_bytes(dequoted: str, expected: bytes) -> None:
    # When
    actual = bytes_encode(dequoted)

    # Then
    assert actual == expected


@pytest.mark.parametrize(
    'expected, encoded',
    BYTES_ENCODE_TEST_DATA,
    ids=[dequoted for dequoted, *_ in BYTES_ENCODE_TEST_DATA],
)
def test_decode_bytes(expected: str, encoded: bytes) -> None:
    # When
    actual = bytes_decode(encoded)

    # Then
    assert actual == expected


ENQUOTE_BYTES_TEST_DATA: Final = tuple((enquoted, dequoted) for enquoted, dequoted, _ in BASE_TEST_DATA)


@pytest.mark.parametrize(
    'expected,dequoted',
    ENQUOTE_BYTES_TEST_DATA,
    ids=[enquoted for enquoted, *_ in ENQUOTE_BYTES_TEST_DATA],
)
def test_enquote_bytes(expected: str, dequoted: str) -> None:
    # When
    actual = enquote_bytes(dequoted)

    # Then
    assert actual == expected


DEQUOTE_BYTES_TEST_DATA: Final = ENQUOTE_BYTES_TEST_DATA + (
    # enquoted, dequoted
    (r'\x0c', '\f'),
    (r'\x24', '$'),
    (r'\x4e80', 'N80'),
)


@pytest.mark.parametrize(
    'enquoted,expected',
    DEQUOTE_BYTES_TEST_DATA,
    ids=[enquoted for enquoted, *_ in DEQUOTE_BYTES_TEST_DATA],
)
def test_dequote_bytes(enquoted: str, expected: str) -> None:
    # When
    actual = dequote_bytes(enquoted)

    # Then
    assert actual == expected


ENQUOTE_STRING_TEST_DATA: Final = ENQUOTE_BYTES_TEST_DATA + (
    # enquoted, dequoted
    (r'\u03b1', 'α'),
    (r'\u4e80', '亀'),
    (r'\U0001f642', '🙂'),
    (r'\u6b66\u5929\u8001\u5e2b', '武天老師'),
    (r'a\n\u03b1\n', 'a\nα\n'),
)


@pytest.mark.parametrize(
    'expected,dequoted',
    ENQUOTE_STRING_TEST_DATA,
    ids=[expected for expected, *_ in ENQUOTE_STRING_TEST_DATA],
)
def test_enquote_string(expected: str, dequoted: str) -> None:
    # When
    actual = enquote_string(dequoted)

    # Then
    assert actual == expected


DEQUOTE_STRING_TEST_DATA: Final = DEQUOTE_BYTES_TEST_DATA + (
    # enquoted, dequoted
    (r'\u0024', '$'),
    (r'\U00000024', '$'),
)


@pytest.mark.parametrize(
    'enquoted,expected',
    DEQUOTE_STRING_TEST_DATA,
    ids=[enquoted for enquoted, *_ in DEQUOTE_STRING_TEST_DATA],
)
def test_dequote_string(enquoted: str, expected: str) -> None:
    # When
    actual = dequote_string(enquoted)

    # Then
    assert actual == expected
