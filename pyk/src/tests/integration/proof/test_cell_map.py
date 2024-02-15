from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KToken, KVariable, build_assoc
from pyk.kcfg.show import KCFGShow
from pyk.proof import APRProof, APRProver, ProofStatus
from pyk.proof.show import APRProofNodePrinter
from pyk.testing import KCFGExploreTest, KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.kast import KInner
    from pyk.kcfg import KCFGExplore
    from pyk.ktool.kprint import KPrint
    from pyk.ktool.kprove import KProve

_LOGGER: Final = logging.getLogger(__name__)


class State(NamedTuple):
    pgm: str
    active_accounts: str
    accounts: Iterable[tuple[str, str]]


EXECUTE_TEST_DATA: Final[Iterable[tuple[str, int, State, int, State, Iterable[State]]]] = (
    (
        'account-nonexistent',
        1,
        State('#accountNonexistent(1)', 'SetItem(1)', [('1', '2')]),
        1,
        State('false', 'SetItem(1)', [('1', '2')]),
        [],
    ),
)


APR_PROVE_TEST_DATA: Iterable[tuple[str, Path, str, str, int | None, int | None]] = (
    ('cell-map-no-branch', K_FILES / 'cell-map-spec.k', 'CELL-MAP-SPEC', 'cell-map-no-branch', 2, 1),
)


class TestCellMapProof(KCFGExploreTest, KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'cell-map.k'

    @staticmethod
    def config(kprint: KPrint, k: str, active_accounts: str, accounts: Iterable[tuple[str, str]]) -> CTerm:
        def _parse(kt: KToken) -> KInner:
            return kprint.parse_token(kt, as_rule=True)

        _k_parsed = _parse(KToken(k, 'KItem'))
        _active_accounts = _parse(KToken(active_accounts, 'Set'))
        _accounts_parsed = (
            KApply(
                'AccountCellMapItem',
                KApply('<id>', _parse(KToken(act_id, 'Int'))),
                KApply(
                    '<account>',
                    KApply('<id>', _parse(KToken(act_id, 'Int'))),
                    KApply('<balance>', _parse(KToken(act_state, 'Int'))),
                ),
            )
            for act_id, act_state in accounts
        )
        _accounts = build_assoc(KApply('.AccountCellMap'), '_AccountCellMap_', _accounts_parsed)
        return CTerm(
            KApply(
                '<generatedTop>',
                KApply('<k>', KSequence(_k_parsed)),
                KApply('<activeAccounts>', _active_accounts),
                KApply('<accounts>', _accounts),
                KVariable('GENERATED_COUNTER_CELL'),
            ),
        )

    @pytest.mark.parametrize(
        'test_id,depth,pre,expected_depth,expected_post,expected_next_states',
        EXECUTE_TEST_DATA,
        ids=[test_id for test_id, *_ in EXECUTE_TEST_DATA],
    )
    def test_execute(
        self,
        kcfg_explore: KCFGExplore,
        test_id: str,
        depth: int,
        pre: State,
        expected_depth: int,
        expected_post: State,
        expected_next_states: Iterable[State],
    ) -> None:
        # Given
        k, aacounts, accounts = pre
        expected_k, _, _ = expected_post

        # When
        exec_res = kcfg_explore.cterm_execute(self.config(kcfg_explore.kprint, k, aacounts, accounts), depth=depth)
        actual_k = kcfg_explore.kprint.pretty_print(exec_res.state.cell('K_CELL'))
        actual_depth = exec_res.depth

        # Then
        assert actual_depth == expected_depth
        assert actual_k == expected_k

    @pytest.mark.parametrize(
        'test_id,spec_file,spec_module,claim_id,max_iterations,max_depth',
        APR_PROVE_TEST_DATA,
        ids=[test_id for test_id, *_ in APR_PROVE_TEST_DATA],
    )
    def test_all_path_reachability_prove(
        self,
        kprove: KProve,
        kcfg_explore: KCFGExplore,
        test_id: str,
        spec_file: str,
        spec_module: str,
        claim_id: str,
        max_iterations: int,
        max_depth: int,
    ) -> None:
        claim = single(
            kprove.get_claims(Path(spec_file), spec_module_name=spec_module, claim_labels=[f'{spec_module}.{claim_id}'])
        )

        proof = APRProof.from_claim(kprove.definition, claim, logs={})
        init = proof.kcfg.node(proof.init)
        new_init_term = kcfg_explore.cterm_assume_defined(init.cterm)
        proof.kcfg.replace_node(init.id, new_init_term)
        prover = APRProver(proof, kcfg_explore=kcfg_explore, execute_depth=max_depth)
        prover.advance_proof(max_iterations=max_iterations)

        kcfg_show = KCFGShow(
            kcfg_explore.kprint, node_printer=APRProofNodePrinter(proof, kcfg_explore.kprint, full_printer=True)
        )
        cfg_lines = kcfg_show.show(proof.kcfg)
        _LOGGER.info('\n'.join(cfg_lines))

        assert proof.status == ProofStatus.PASSED
