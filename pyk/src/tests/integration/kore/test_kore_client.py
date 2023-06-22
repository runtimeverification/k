from __future__ import annotations

from string import Template
from typing import TYPE_CHECKING

import pytest

from pyk.kore.parser import KoreParser
from pyk.kore.prelude import BOOL, INT, TRUE, and_bool, eq_int, gt_int, int_dv, le_int
from pyk.kore.rpc import (
    BranchingResult,
    CutPointResult,
    DepthBoundResult,
    ImpliesResult,
    KoreClientError,
    SatResult,
    State,
    StuckResult,
    TerminalResult,
    UnknownResult,
    UnsatResult,
)
from pyk.kore.syntax import And, Bottom, Equals, EVar, Implies, Module, Top
from pyk.testing import KoreClientTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Mapping
    from typing import Any, Final

    from pyk.kore.rpc import ExecuteResult, GetModelResult, KoreClient
    from pyk.kore.syntax import Pattern

int_top = Top(INT)
int_bottom = Bottom(INT)
x, y = (EVar(v, INT) for v in ['x', 'y'])


def term(n: int) -> Pattern:
    template = Template(
        r"""
        Lbl'-LT-'generatedTop'-GT-'{}(
            Lbl'-LT-'k'-GT-'{}(
                kseq{}(
                    inj{SortInt{}, SortKItem{}}(
                        \dv{SortInt{}}("$n")
                    ),
                    K:SortK{}
                )
            ),
            GCC:SortGeneratedCounterCell{}
        )
        """
    )
    parser = KoreParser(template.substitute(n=n))
    pattern = parser.pattern()
    assert parser.eof
    return pattern


def state(n: int) -> State:
    return State(term=term(n), substitution=None, predicate=None)


EXECUTE_TEST_DATA: Final[tuple[tuple[str, int, Mapping[str, Any], ExecuteResult], ...]] = (
    ('branching', 0, {}, BranchingResult(state=state(2), depth=2, next_states=(state(4), state(3)), logs=())),
    ('depth-bound', 0, {'max_depth': 2}, DepthBoundResult(state=state(2), depth=2, logs=())),
    ('stuck', 4, {}, StuckResult(state=state(6), depth=2, logs=())),
    (
        'cut-point',
        4,
        {'cut_point_rules': ['KORE-RPC-TEST.r56']},
        CutPointResult(state=state(5), depth=1, next_states=(state(6),), rule='KORE-RPC-TEST.r56', logs=()),
    ),
    (
        'terminal',
        4,
        {'terminal_rules': ['KORE-RPC-TEST.r56']},
        TerminalResult(state=state(6), depth=2, rule='KORE-RPC-TEST.r56', logs=()),
    ),
)


IMPLIES_TEST_DATA: Final = (
    (
        '0 -> T',
        int_dv(0),
        int_top,
        ImpliesResult(True, Implies(INT, int_dv(0), int_top), int_top, int_top, ()),
    ),
    ('0 -> 1', int_dv(0), int_dv(1), ImpliesResult(False, Implies(INT, int_dv(0), int_dv(1)), None, None, ())),
    (
        'X -> 0',
        x,
        int_dv(0),
        ImpliesResult(
            False,
            Implies(INT, x, int_dv(0)),
            Equals(
                op_sort=INT,
                sort=INT,
                left=x,
                right=int_dv(0),
            ),
            int_top,
            (),
        ),
    ),
    ('X -> X', x, x, ImpliesResult(True, Implies(INT, x, x), int_top, int_top, ())),
)

IMPLIES_ERROR_TEST_DATA: Final = (
    ('0 -> X', int_dv(0), x),
    ('X -> Y', x, y),
)

SIMPLIFY_TEST_DATA: Final = (('top-and-top', And(INT, int_top, int_top), int_top),)

GET_MODEL_TEST_DATA: Final = (
    ('unkown-config', term(0), None, UnknownResult()),
    ('unknown-trivial', int_top, None, UnknownResult()),
    ('unsat-trivial', int_bottom, None, UnsatResult()),
    ('unsat-ineq', Equals(BOOL, INT, TRUE, and_bool(gt_int(x, int_dv(1)), le_int(x, int_dv(0)))), None, UnsatResult()),
    ('unsat-eq', Equals(BOOL, INT, TRUE, and_bool(eq_int(x, int_dv(0)), eq_int(x, int_dv(1)))), None, UnsatResult()),
    (
        'unsat-eq-ml',
        And(INT, Equals(BOOL, INT, TRUE, eq_int(x, int_dv(0))), Equals(BOOL, INT, TRUE, eq_int(x, int_dv(1)))),
        None,
        UnsatResult(),
    ),
    (
        'sat-ineq',
        Equals(BOOL, INT, TRUE, and_bool(gt_int(x, int_dv(0)), le_int(x, int_dv(1)))),
        None,
        SatResult(Equals(INT, INT, x, int_dv(1))),
    ),
    (
        'sat-ineq-ml',
        And(INT, Equals(BOOL, INT, TRUE, gt_int(x, int_dv(0))), Equals(BOOL, INT, TRUE, le_int(x, int_dv(1)))),
        None,
        SatResult(Equals(INT, INT, x, int_dv(1))),
    ),
    (
        'sat-eq-single-var',
        Equals(BOOL, INT, TRUE, eq_int(x, int_dv(0))),
        None,
        SatResult(Equals(INT, INT, x, int_dv(0))),
    ),
    (
        'sat-eq-two-vars',
        Equals(BOOL, INT, TRUE, and_bool(eq_int(x, int_dv(0)), eq_int(y, int_dv(1)))),
        None,
        SatResult(And(INT, Equals(INT, INT, x, int_dv(0)), Equals(INT, INT, y, int_dv(1)))),
    ),
)

ADD_MODULE_TEST_DATA: Final = (('empty-module', Module('HELLO')),)


class TestKoreClient(KoreClientTest):
    KOMPILE_MAIN_FILE = K_FILES / 'kore-rpc-test.k'
    KORE_MODULE_NAME = 'KORE-RPC-TEST'

    @pytest.mark.parametrize(
        'test_id,n,params,expected',
        EXECUTE_TEST_DATA,
        ids=[test_id for test_id, *_ in EXECUTE_TEST_DATA],
    )
    def test_execute(
        self,
        kore_client: KoreClient,
        test_id: str,
        n: int,
        params: Mapping[str, Any],
        expected: ExecuteResult,
    ) -> None:
        # When
        actual = kore_client.execute(term(n), **params)

        # Then
        assert actual == expected

    @pytest.mark.parametrize(
        'test_id,antecedent,consequent,expected',
        IMPLIES_TEST_DATA,
        ids=[test_id for test_id, *_ in IMPLIES_TEST_DATA],
    )
    def test_implies(
        self,
        kore_client: KoreClient,
        test_id: str,
        antecedent: Pattern,
        consequent: Pattern,
        expected: ImpliesResult,
    ) -> None:
        # When
        actual = kore_client.implies(antecedent, consequent)

        # Then
        assert actual == expected

    @pytest.mark.parametrize(
        'test_id,antecedent,consequent',
        IMPLIES_ERROR_TEST_DATA,
        ids=[test_id for test_id, *_ in IMPLIES_ERROR_TEST_DATA],
    )
    def test_implies_error(
        self,
        kore_client: KoreClient,
        test_id: str,
        antecedent: Pattern,
        consequent: Pattern,
    ) -> None:
        with pytest.raises(KoreClientError) as excinfo:
            # When
            kore_client.implies(antecedent, consequent)

        # Then
        assert excinfo.value.code == 4

    @pytest.mark.parametrize(
        'test_id,pattern,expected',
        SIMPLIFY_TEST_DATA,
        ids=[test_id for test_id, *_ in SIMPLIFY_TEST_DATA],
    )
    def test_simplify(
        self,
        kore_client: KoreClient,
        test_id: str,
        pattern: Pattern,
        expected: Pattern,
    ) -> None:
        # When
        actual, _logs = kore_client.simplify(pattern)

        # Then
        assert actual == expected

    @pytest.mark.parametrize(
        'test_id,pattern,module_name,expected',
        GET_MODEL_TEST_DATA,
        ids=[test_id for test_id, *_ in GET_MODEL_TEST_DATA],
    )
    def test_get_model(
        self,
        kore_client: KoreClient,
        test_id: str,
        pattern: Pattern,
        module_name: str | None,
        expected: GetModelResult,
    ) -> None:
        # When
        actual = kore_client.get_model(pattern, module_name)

        # Then
        assert actual == expected

    @pytest.mark.parametrize(
        'test_id,module',
        ADD_MODULE_TEST_DATA,
        ids=[test_id for test_id, *_ in ADD_MODULE_TEST_DATA],
    )
    def test_add_module(
        self,
        kore_client: KoreClient,
        test_id: str,
        module: Module,
    ) -> None:
        kore_client.add_module(module)
