from __future__ import annotations

import json
from itertools import count
from typing import TYPE_CHECKING

import pytest

import pyk.kore.match as km
from pyk.kore.prelude import (
    KSEQ,
    LBL_GENERATED_TOP,
    LBL_K,
    SORT_JSON,
    SORT_K_ITEM,
    STRING,
    generated_counter,
    generated_top,
    inj,
    int_dv,
    json2string,
    json_to_kore,
    k,
    kore_to_json,
    kseq,
    str_dv,
    string2json,
)
from pyk.testing import KRunTest
from pyk.utils import chain

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Any, Final

    from pyk.kore.syntax import Pattern
    from pyk.ktool.krun import KRun


TEST_DATA: Final[tuple[Any, ...]] = (
    None,
    False,
    0,
    '',
    [],
    {},
    True,
    1,
    '0',
    '1',
    'a',
    [None],
    [True],
    ['a'],
    ['a', 'b'],
    [0, 1, 2],
    [0, '', {}, [], None],
    {'a': 1},
    {'a': 'b'},
    {'a': None},
    {'a': True, 'b': False},
    {'a': 1, 'b': 2, 'c': 3},
    {'a': {}},
    {'a': []},
    {'a': {'b': {'c': {}}}},
    {'a': ['b', 'c']},
    {'a': [{'b': 2}, {'c': 3}]},
    [{'a': 1}, {'b': 2}, {'c': 3}],
)


class TestJsonToKore(KRunTest):
    KOMPILE_DEFINITION = """
        requires "json.md"

        module JSON-TEST
            imports STRING-SYNTAX
            imports JSON
            syntax Pgm ::= String | JSON
            configuration <k> $PGM:Pgm</k>
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'JSON-TEST'
    KOMPILE_ARGS = {'syntax_module': 'JSON-TEST'}

    @pytest.mark.parametrize('json_data', TEST_DATA, ids=count())
    def test_json_to_kore(self, krun: KRun, json_data: Any) -> None:
        # When
        json_pattern = json_to_kore(json_data)
        init_config = _config((inj(STRING, SORT_K_ITEM, json2string(json_pattern)),))
        final_config = krun.run_pattern(init_config)
        string_pattern = _extract(final_config)
        json_text = km.kore_str(string_pattern)
        actual_data = json.loads(json_text)

        # Then
        assert actual_data == json_data

    @pytest.mark.parametrize('json_data', TEST_DATA, ids=count())
    def test_kore_to_json(self, krun: KRun, json_data: Any) -> None:
        # When
        json_text = json.dumps(json_data)
        string_pattern = str_dv(json_text)
        init_config = _config((inj(SORT_JSON, SORT_K_ITEM, string2json(string_pattern)),))
        final_config = krun.run_pattern(init_config)
        json_pattern = _extract(final_config)
        actual_data = kore_to_json(json_pattern)

        # Then
        assert actual_data == json_data


def _config(kitems: Iterable[Pattern]) -> Pattern:
    return generated_top(
        (
            k(kseq(kitems)),
            generated_counter(int_dv(0)),
        ),
    )


def _extract(config: Pattern) -> Pattern:
    extract = (
        chain >> km.app(LBL_GENERATED_TOP.value) >> km.arg(LBL_K.value) >> km.arg(KSEQ.value) >> km.arg(0) >> km.inj
    )
    return extract(config)
