from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kore.prelude import BOOL, INT, TRUE, eq_int, int_dv
from pyk.kore.rpc import SatResult
from pyk.kore.syntax import App, Equals, EVar
from pyk.testing import KoreClientTest

if TYPE_CHECKING:
    from typing import Final

    from pyk.kore.rpc import KoreClient

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

kore_for = {'/Int': "Lbl'UndsSlsh'Int'Unds'", '%Int': "Lbl'UndsPerc'Int'Unds'"}


class TestDivisionHooksHs(KoreClientTest):
    KOMPILE_DEFINITION = """
        module SMT
            imports INT
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'SMT'
    KOMPILE_ARGS = {'syntax_module': 'SMT'}
    LLVM_ARGS = {'syntax_module': 'SMT'}

    @pytest.mark.parametrize(
        'op, a, b, c',
        T_DIVISION_TEST_DATA,
        ids=[f'get-model: {a} {op} {b} == {c}' for op, a, b, c in T_DIVISION_TEST_DATA],
    )
    def test_smt_t_division(self, kore_client: KoreClient, op: str, a: int, b: int, c: int) -> None:
        """checks whether the SMT solver returns ``X = c`` for ``X = a op b``."""

        # Given
        pattern = Equals(
            BOOL,
            INT,
            TRUE,
            eq_int(App(kore_for[op], (), (int_dv(a), int_dv(b))), EVar('X', INT)),
        )

        # When
        actual = kore_client.get_model(pattern, None)

        # Then
        expected = SatResult(Equals(INT, INT, EVar('X', INT), int_dv(c)))

        assert actual == expected

    @pytest.mark.parametrize(
        'op, a, b, c',
        T_DIVISION_TEST_DATA,
        ids=[f'simplify: {a} {op} {b} == {c}' for op, a, b, c in T_DIVISION_TEST_DATA],
    )
    def test_llvm_t_division(self, kore_client: KoreClient, op: str, a: int, b: int, c: int) -> None:
        """checks whether kore-rpc (HS hook) and booster (LLVM library) both return ``c`` for ``a op b``."""

        # Given
        pattern = App(kore_for[op], (), (int_dv(a), int_dv(b)))

        # When
        actual = kore_client.simplify(pattern)

        # Then
        expected = (int_dv(c), ())

        assert actual == expected
