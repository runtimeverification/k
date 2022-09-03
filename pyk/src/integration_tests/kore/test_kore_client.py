from string import Template
from typing import Any, Final, Mapping, Tuple

from pyk.kore.client import BranchingResult, DepthBoundResult, ExecuteResult, ImpliesResult, State, StuckResult
from pyk.kore.parser import KoreParser
from pyk.kore.syntax import DV, Implies, Pattern, SortApp, String, Top

from .kore_client_test import KoreClientTest


def term(n: int) -> Pattern:
    template = Template(
        r'''
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
    '''
    )
    parser = KoreParser(template.substitute(n=n))
    pattern = parser.pattern()
    assert parser.eof
    return pattern


def state(n: int) -> State:
    return State(term=term(n), substitution=None, predicate=None)


class SimpleKoreClientTest(KoreClientTest):
    KOMPILE_MAIN_FILE = 'k-files/kore-rpc-test.k'
    KORE_MODULE_NAME = 'KORE-RPC-TEST'

    def test_execute(self):
        # Given
        test_data: Final[Tuple[Tuple[int, Mapping[str, Any], ExecuteResult], ...]] = (
            ('branching', 0, {}, BranchingResult(state=state(2), depth=2, next_states=(state(4), state(3)))),
            ('depth-bound', 0, {'max_depth': 2}, DepthBoundResult(state=state(2), depth=2)),
            ('stuck', 4, {}, StuckResult(state=state(6), depth=2)),
        )

        for test_name, n, params, expected in test_data:
            with self.subTest(test_name):
                # When
                actual = self.client.execute(term(n), **params)

                # Then
                self.assertEqual(actual, expected)

    def test_implies(self):
        # Given
        test_data = (
            (
                '0 -> T',
                int_dv(0),
                int_top,
                ImpliesResult(True, Implies(int_sort, int_dv(0), int_top), int_top, int_top),
            ),
            ('0 -> 1', int_dv(0), int_dv(1), ImpliesResult(False, Implies(int_sort, int_dv(0), int_dv(1)), None, None)),
        )

        for test_name, antecedent, consequent, expected in test_data:
            with self.subTest(test_name):
                # When
                actual = self.client.implies(antecedent, consequent)

                # Then
                self.assertEqual(actual, expected)


int_sort = SortApp('SortInt')
int_top = Top(int_sort)


def int_dv(n: int) -> DV:
    return DV(int_sort, String(str(n)))
