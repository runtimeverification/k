from string import Template
from typing import Any, Final, Mapping, Tuple

from pyk.kore.client import BranchingResult, DepthBoundResult, ExecuteResult, State, StuckResult
from pyk.kore.parser import KoreParser
from pyk.kore.syntax import Pattern

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

    TEST_DATA: Final[Tuple[Tuple[int, Mapping[str, Any], ExecuteResult], ...]] = (
        (0, {}, BranchingResult(state=state(2), depth=2, next_states=(state(4), state(3)))),
        (0, {'max_depth': 2}, DepthBoundResult(state=state(2), depth=2)),
        (4, {}, StuckResult(state=state(6), depth=2)),
    )

    def test_execute(self):
        for i, (n, params, expected) in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                # When
                actual = self.client.execute(term(n), **params)

                # Then
                self.assertEqual(actual, expected)
