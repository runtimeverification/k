from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kore.prelude import (
    BOOL,
    INT,
    SORT_K_ITEM,
    TRUE,
    eq_int,
    generated_counter,
    generated_top,
    inj,
    int_dv,
    k,
    kseq,
)
from pyk.kore.rpc import SatResult
from pyk.kore.syntax import App, Equals, EVar
from pyk.ktool.krun import llvm_interpret
from pyk.testing import KompiledTest, KoreClientTest

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pyk.kore.rpc import KoreClient
    from pyk.kore.syntax import Pattern


T_DIVISION_TEST_DATA: Final = (
    # Op   ,  a,  b, a Op b
    ('/Int', +8, +3, +2),
    ('/Int', +8, -3, -2),
    ('/Int', -8, +3, -2),
    ('/Int', -8, -3, +2),
    ('%Int', +8, +3, +2),
    ('%Int', +8, -3, +2),
    ('%Int', -8, +3, -2),
    ('%Int', -8, -3, -2),
    #####################
    ('/Int', +1, +2, 0),
    ('/Int', +1, -2, 0),
    ('/Int', -1, +2, 0),
    ('/Int', -1, -2, 0),
    ('%Int', +1, +2, +1),
    ('%Int', +1, -2, +1),
    ('%Int', -1, +2, -1),
    ('%Int', -1, -2, -1),
    #####################
    ('/Int', +4, +2, +2),
    ('/Int', +4, -2, -2),
    ('/Int', -4, +2, -2),
    ('/Int', -4, -2, +2),
    ('%Int', +4, +2, 0),
    ('%Int', +4, -2, 0),
    ('%Int', -4, +2, 0),
    ('%Int', -4, -2, 0),
)
IDS: Final = tuple(f'{a} {op} {b} == {c}' for op, a, b, c in T_DIVISION_TEST_DATA)
DEFINITION = """
    module SMT
        imports INT
    endmodule
"""


def div_pattern(op: str, a: int, b: int) -> App:
    kore_for = {
        '/Int': "Lbl'UndsSlsh'Int'Unds'",
        '%Int': "Lbl'UndsPerc'Int'Unds'",
    }
    return App(kore_for[op], (), (int_dv(a), int_dv(b)))


def config(pgm: Pattern) -> App:
    return generated_top(
        (
            k(
                kseq(
                    (inj(INT, SORT_K_ITEM, pgm),),
                )
            ),
            generated_counter(int_dv(0)),
        ),
    )


class TestDivisionHooksLlvm(KompiledTest):
    KOMPILE_DEFINITION = DEFINITION
    KOMPILE_MAIN_MODULE = 'SMT'
    KOMPILE_ARGS = {'syntax_module': 'SMT'}

    @pytest.mark.parametrize('op, a, b, c', T_DIVISION_TEST_DATA, ids=IDS)
    def test(self, definition_dir: Path, op: str, a: int, b: int, c: int) -> None:
        # Given
        pattern = config(div_pattern(op, a, b))
        expected = config(int_dv(c))

        # When
        actual = llvm_interpret(definition_dir, pattern)

        # Then
        assert actual == expected


class TestDivisionHooksHs(KoreClientTest):
    KOMPILE_DEFINITION = DEFINITION
    KOMPILE_MAIN_MODULE = 'SMT'
    KOMPILE_ARGS = {'syntax_module': 'SMT'}
    LLVM_ARGS = {'syntax_module': 'SMT'}

    @pytest.mark.parametrize('op, a, b, c', T_DIVISION_TEST_DATA, ids=IDS)
    def test_get_model(self, kore_client: KoreClient, op: str, a: int, b: int, c: int) -> None:
        """Check whether the SMT solver returns ``X = c`` for ``X = a op b``."""

        # Given
        pattern = Equals(
            BOOL,
            INT,
            TRUE,
            eq_int(div_pattern(op, a, b), EVar('X', INT)),
        )
        expected = SatResult(Equals(INT, INT, EVar('X', INT), int_dv(c)))

        # When
        actual = kore_client.get_model(pattern)

        # Then
        assert actual == expected

    @pytest.mark.parametrize('op, a, b, c', T_DIVISION_TEST_DATA, ids=IDS)
    def test_simplify(self, kore_client: KoreClient, op: str, a: int, b: int, c: int) -> None:
        """Check whether kore-rpc (HS hook) and booster (LLVM library) both return ``c`` for ``a op b``."""

        # Given
        pattern = div_pattern(op, a, b)
        expected = (int_dv(c), ())

        # When
        actual = kore_client.simplify(pattern)

        # Then
        assert actual == expected
