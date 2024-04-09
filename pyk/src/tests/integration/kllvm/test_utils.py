from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm.utils import get_requires
from pyk.kore.parser import KoreParser

if TYPE_CHECKING:
    from typing import Final

AXIOM_TEST_DATA: Final = (
    (
        'axiom1',
        r'W{}(VarA : SortInt{},\dv{SortInt{}}("1"))',
        r'axiom {} \rewrites{SortGeneratedTopCell{}}(\and{SortGeneratedTopCell{}}(X{}(Y{}(kseq{}(inj{SortInt{}, SortKItem{}}(VarA : SortInt{}),dotk{}())), Z : SortGeneratedCounterCell{}),\equals{SortBool{}, SortGeneratedTopCell{}}(W{}(VarA : SortInt{},\dv{SortInt{}}("1")),\dv{SortBool{}}("true"))),\and{SortGeneratedTopCell{}}(X{}(Y{}(kseq{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")),dotk{}())),),\top{SortGeneratedTopCell{}}())) []',
    ),
)


@pytest.mark.parametrize(
    'test_id,kore_requires,kore_axiom', AXIOM_TEST_DATA, ids=[test_id for test_id, *_ in AXIOM_TEST_DATA]
)
def test_get_requires(test_id: str, kore_requires: str, kore_axiom: str) -> None:
    # Given
    axiom = KoreParser(kore_axiom).axiom()
    expected_requires = KoreParser(kore_requires).pattern()

    # When
    actual_requires = get_requires(axiom)

    # Then
    assert actual_requires == expected_requires
