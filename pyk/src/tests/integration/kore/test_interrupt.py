from __future__ import annotations

import threading
import time
from string import Template
from typing import TYPE_CHECKING

from pyk.kore.parser import KoreParser
from pyk.kore.rpc import DefaultError
from pyk.testing import KoreClientTest

if TYPE_CHECKING:
    from pyk.kore.rpc import KoreClient
    from pyk.kore.syntax import Pattern


def term(n: int) -> Pattern:
    template = Template(
        r"""
        Lbl'-LT-'generatedTop'-GT-'{}(
            Lbl'-LT-'k'-GT-'{}(
                kseq{}(
                    inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("$n")),
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


class TestInterrupt(KoreClientTest):
    # The interrupt mechanism (cancel over the single-socket transport) is what `advance_proof`'s
    # step-timeout policy relies on. `inc` never terminates, so an `execute` only ever returns by
    # being interrupted -- which is exactly what this test asserts.
    DISABLE_BOOSTER = True  # exercise the legacy (pure haskell) kore-rpc server

    KOMPILE_DEFINITION = """
        module INTERRUPT-TEST
            imports INT
            rule [inc]: I:Int => I +Int 1
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'INTERRUPT-TEST'
    KOMPILE_ARGS = {'syntax_module': 'INTERRUPT-TEST'}

    def test_interrupt_aborts_in_flight_request_and_keeps_connection(self, kore_client: KoreClient) -> None:
        # Given: a non-terminating `execute` running on another thread.
        box: dict = {}

        def run() -> None:
            try:
                kore_client.execute(term(0), max_depth=1_000_000_000)
            except BaseException as e:  # noqa: B036  - record whatever the interrupted call raises
                box['exc'] = e

        thread = threading.Thread(target=run, daemon=True)
        thread.start()
        time.sleep(2.0)  # let the step get well underway
        assert thread.is_alive()  # sanity: it is genuinely long-running, not terminating on its own

        # When: the in-flight request is interrupted.
        kore_client.interrupt()

        # Then: the call is aborted promptly (rather than running ~1e9 steps to completion)...
        thread.join(timeout=10.0)
        assert not thread.is_alive(), 'execute() was not aborted by interrupt() within 10s'
        exc = box.get('exc')
        assert isinstance(exc, DefaultError)
        assert exc.message == 'Request cancelled'

        # ...and the connection survives the cancel: a fresh request still succeeds on it.
        result = kore_client.execute(term(0), max_depth=1)
        assert result.depth == 1
