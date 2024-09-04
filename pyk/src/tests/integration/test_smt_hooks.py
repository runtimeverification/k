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
    # Op   ,  a,  b, a Op b, OpKore
    ('/Int', +8, +3, +2, "Lbl'UndsSlsh'Int'Unds'"),
    ('/Int', +8, -3, -2, "Lbl'UndsSlsh'Int'Unds'"),
    ('/Int', -8, +3, -2, "Lbl'UndsSlsh'Int'Unds'"),
    ('/Int', -8, -3, +2, "Lbl'UndsSlsh'Int'Unds'"),
    ('%Int', +8, +3, +2, "Lbl'UndsPerc'Int'Unds'"),
    ('%Int', +8, -3, +2, "Lbl'UndsPerc'Int'Unds'"),
    ('%Int', -8, +3, -2, "Lbl'UndsPerc'Int'Unds'"),
    ('%Int', -8, -3, -2, "Lbl'UndsPerc'Int'Unds'"),
    ########################
    ('/Int', +1, +2, 0, "Lbl'UndsSlsh'Int'Unds'"),
    ('/Int', +1, -2, 0, "Lbl'UndsSlsh'Int'Unds'"),
    ('/Int', -1, +2, 0, "Lbl'UndsSlsh'Int'Unds'"),
    ('/Int', -1, -2, 0, "Lbl'UndsSlsh'Int'Unds'"),
    ('%Int', +1, +2, +1, "Lbl'UndsPerc'Int'Unds'"),
    ('%Int', +1, -2, +1, "Lbl'UndsPerc'Int'Unds'"),
    ('%Int', -1, +2, -1, "Lbl'UndsPerc'Int'Unds'"),
    ('%Int', -1, -2, -1, "Lbl'UndsPerc'Int'Unds'"),
    ########################
    ('/Int', +4, +2, +2, "Lbl'UndsSlsh'Int'Unds'"),
    ('/Int', +4, -2, -2, "Lbl'UndsSlsh'Int'Unds'"),
    ('/Int', -4, +2, -2, "Lbl'UndsSlsh'Int'Unds'"),
    ('/Int', -4, -2, +2, "Lbl'UndsSlsh'Int'Unds'"),
    ('%Int', +4, +2, 0, "Lbl'UndsPerc'Int'Unds'"),
    ('%Int', +4, -2, 0, "Lbl'UndsPerc'Int'Unds'"),
    ('%Int', -4, +2, 0, "Lbl'UndsPerc'Int'Unds'"),
    ('%Int', -4, -2, 0, "Lbl'UndsPerc'Int'Unds'"),
)


class TestSMTHooks(KoreClientTest):
    KOMPILE_DEFINITION = """
        module SMT
            imports INT
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'SMT'
    KOMPILE_ARGS = {'syntax_module': 'SMT'}
    LLVM_ARGS = {'syntax_module': 'SMT'}

    @pytest.mark.parametrize(
        'rel, a, b, c, rel_kore',
        T_DIVISION_TEST_DATA,
        ids=[f'{a} {r} {b} == {c}' for r, a, b, c, _ in T_DIVISION_TEST_DATA],
    )
    def test_smt_t_division(self, kore_client: KoreClient, rel: str, rel_kore: str, a: int, b: int, c: int) -> None:

        # checks whether the SMT solver returns X = c for X = a rel b
        pattern = Equals(
            BOOL,
            INT,
            TRUE,
            eq_int(App(rel_kore, (), (int_dv(a), int_dv(b))), EVar('x', INT)),
        )

        expected = SatResult(Equals(INT, INT, EVar('x', INT), int_dv(c)))

        # When
        actual = kore_client.get_model(pattern, None)

        # Then
        assert actual == expected
