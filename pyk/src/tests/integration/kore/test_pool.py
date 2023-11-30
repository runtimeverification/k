from __future__ import annotations

import time
from typing import TYPE_CHECKING

from pyk.kore import match as km
from pyk.kore.prelude import (
    KSEQ,
    LBL_GENERATED_TOP,
    LBL_K,
    SORT_K_ITEM,
    STRING,
    dv,
    generated_counter,
    generated_top,
    inj,
    k,
    kseq,
)
from pyk.kore.rpc import BranchingResult, KoreClient, StuckResult
from pyk.testing import KoreServerPoolTest
from pyk.utils import chain

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.kore.pool import KoreServerPool


class TestKoreServerPool(KoreServerPoolTest):
    KOMPILE_MAIN_FILE = K_FILES / 'tree-ts.k'

    POOL_MODULE_NAME = 'TREE-TS'
    POOL_MAX_WORKERS = 4

    def test(self, server_pool: KoreServerPool) -> None:
        # Given
        expected = {'', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aaa', 'aab', 'aba', 'abb', 'baa', 'bab', 'bba', 'bbb'}

        # When
        actual = explore(server_pool)

        # Then
        assert actual == expected


def explore(pool: KoreServerPool) -> set[str]:
    init_future = pool.submit(expand, '')
    pending = {init_future}
    visited = {''}

    while pending:
        current_future = next((future for future in pending if future.done()), None)

        if current_future is None:
            time.sleep(0.1)
            continue

        next_states = current_future.result()
        for next_state in next_states:
            visited.add(next_state)
            next_future = pool.submit(expand, next_state)
            pending.add(next_future)

        pending.remove(current_future)

    return visited


def expand(port: int, state: str) -> list[str]:
    pattern = generated_top(
        (k(kseq((inj(STRING, SORT_K_ITEM, dv(state)),))), generated_counter(dv(0))),
    )

    with KoreClient(host='localhost', port=port) as client:
        exec_res = client.execute(pattern)

    if isinstance(exec_res, StuckResult):
        return []

    if not isinstance(exec_res, BranchingResult):
        raise AssertionError()

    extract_str = (
        chain
        >> km.app(LBL_GENERATED_TOP.value)
        >> km.arg(LBL_K.value)
        >> km.arg(KSEQ.value)
        >> km.arg(0)
        >> km.inj
        >> km.kore_str
    )

    return [extract_str(state.term) for state in exec_res.next_states]
