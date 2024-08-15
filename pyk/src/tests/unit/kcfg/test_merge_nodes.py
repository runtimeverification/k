from itertools import count
from typing import TYPE_CHECKING, Any, Final
import pytest

from pyk.cterm import CSubst, CTerm
from pyk.kast.inner import KVariable, KApply, KToken
from pyk.kcfg import KCFG
from pyk.kcfg.semantics import DefaultSemantics, KCFGSemantics
from pyk.ktool.kprint import KPrint
from pyk.prelude.kint import geInt, intToken, ltInt
from pyk.prelude.ml import mlAnd, mlEqualsTrue, mlOr

from ..test_kcfg import node_dicts, propagate_split_constraints, split_dicts, x_config, x_subst
from collections.abc import Iterable

from ..utils import TEST_DATA_DIR

from pyk.kcfg.tui import KCFGViewer


x_lt_0 = mlEqualsTrue(ltInt(KVariable('X'), intToken(0)))
x_ge_0 = mlEqualsTrue(geInt(KVariable('X'), intToken(0)))
x_lt_3 = mlEqualsTrue(ltInt(KVariable('X'), intToken(3)))
x_ge_3 = mlEqualsTrue(geInt(KVariable('X'), intToken(3)))
x_lt_4 = mlEqualsTrue(ltInt(KVariable('X'), intToken(4)))
x_ge_4 = mlEqualsTrue(geInt(KVariable('X'), intToken(4)))
x_lt_5 = mlEqualsTrue(ltInt(KVariable('X'), intToken(5)))
x_ge_5 = mlEqualsTrue(geInt(KVariable('X'), intToken(5)))


def edge_dicts(*edges: Iterable) -> list[dict[str, Any]]:
    def _make_edge_dict(
        i: int, j: int, depths: Iterable[int], rules_list: Iterable[Iterable[str]], csubsts: Iterable[CSubst]
    ) -> dict[str, Any]:
        return {
            'source': i,
            'target': j,
            'depths': list(depths),
            'rules_list': [list(rules) for rules in rules_list],
            'csubsts': [csubst.to_dict() for csubst in csubsts],
        }

    return [_make_edge_dict(*edge) for edge in edges]


class TestSemantics(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        return True


def merge_node_test_kcfg() -> KCFG:
    """
    1 -|Split: X >=Int 5|->            2 -|Edge: (5, (r1), #Top)|->                                                        6
      -|Split: X >=Int 3 & X <Int 5|-> 3 -|Edge: (10, (r2,r3), X >=Int 4 & X <Int 5), (15, (r4), X <Int 4 & X >=Int 3 )|-> 7
      -|Split: X >=Int 0 & X <Int 3|-> 4 -|Edge: (20, (r5), #Top)|->                                                       8
      -|Split: X  <Int 0|->            5 -|Edge: (25, (r6), #Top)|->                                                       9
    #Top: CSubst()
    """
    d = {
        'next': 10,
        'nodes': node_dicts(9, config=x_config()),
        'edges': edge_dicts(
            (2, 6, [5], [['r1']], [CSubst()]),
            (
                3,
                7,
                [10, 15],
                [['r2', 'r3'], ['r4']],
                [
                    x_subst().add_constraint(x_ge_4).add_constraint(x_lt_5),
                    x_subst().add_constraint(x_ge_3).add_constraint(x_lt_4),
                ],
            ),
            (4, 8, [20], [['r5']], [CSubst()]),
            (5, 9, [25], [['r6']], [CSubst()]),
        ),
        'splits': split_dicts(
            (1, [(2, x_ge_5), (3, mlAnd([x_ge_3, x_lt_5])), (4, mlAnd([x_ge_0, x_lt_3])), (5, x_lt_0)]),
            csubst=x_subst(),
        ),
    }
    cfg = KCFG.from_dict(d)
    propagate_split_constraints(cfg)
    return cfg


def merge_node_test_kcfg_simple_expected() -> KCFG:
    """
    1 -|Edge: (5, (r1), X >=Int 5),
              (10, (r2,r3), X >=Int 4 & X <Int 5),
              (15, (r4), X <Int 4 & X >=Int 3 ),
              (20, (r5), X >=Int 0 & X <Int 3),
              (25, (r6), X <Int 0)|
      -> 6 | 7 | 8 | 9
      -|Split: X >=Int 5|->            6
      -|Split: X >=Int 3 & X <Int 5|-> 7
      -|Split: X >=Int 0 & X <Int 3|-> 8
      -|Split: X  <Int 0|->            9
    """
    d = {
        'next': 12,
        'nodes': node_dicts(11, config=x_config()),
        'edges': edge_dicts(
            (
                1,
                11,
                [5, 10, 15, 20, 25],
                [['r1'], ['r2', 'r3'], ['r4'], ['r5'], ['r6']],
                [
                    x_subst().add_constraint(x_ge_5),
                    x_subst().add_constraint(x_ge_4).add_constraint(x_lt_5).add_constraint(x_ge_3),
                    x_subst().add_constraint(x_ge_3).add_constraint(x_lt_4).add_constraint(x_lt_5),
                    x_subst().add_constraint(x_lt_3).add_constraint(x_ge_0),
                    x_subst().add_constraint(x_lt_0),
                ],
            )
        ),
        'splits': split_dicts(
            (11, [(6, x_ge_5), (7, mlAnd([x_ge_3, x_lt_5])), (8, mlAnd([x_ge_0, x_lt_3])), (9, x_lt_0)]),
            csubst=x_subst(),
        ),
    }
    cfg = KCFG.from_dict(d)
    propagate_split_constraints(cfg)
    cfg.remove_node(2)
    cfg.remove_node(3)
    cfg.remove_node(4)
    cfg.remove_node(5)
    cfg.remove_node(10)
    return cfg


class TestSemanticsIncomplete(DefaultSemantics):
    def is_mergeable(self, c1: CTerm, c2: CTerm) -> bool:
        # X >=Int 3 mergeable
        if len(c1.constraints) == 0 or len(c2.constraints) == 0:
            return False

        x = x_subst()
        cases = [
            x.add_constraint(x_ge_5),
            x.add_constraint(mlAnd([x_lt_5, x_ge_3])),
        ]

        def _check(c: CTerm) -> bool:
            return any(case.constraints == c.constraints for case in cases)

        return _check(c1) and _check(c2)


def merge_node_test_kcfg_incomplete_expected() -> KCFG:
    """
    1 -|Split|> 4 -|Edge|> 8
              > 5 -|Edge|> 9
              > 2 | 3 -|Edge|> 6 | 7  -|Split|> 6 , 7
    """
    d = {
        'next': 12,
        'nodes': node_dicts(11, config=x_config()),
        'edges': edge_dicts(
            (4, 8, [20], [['r5']], [CSubst()]),
            (5, 9, [25], [['r6']], [CSubst()]),
            (
                10,
                11,
                [5, 10, 15],
                [['r1'], ['r2', 'r3'], ['r4']],
                [
                    x_subst().add_constraint(x_ge_5),
                    x_subst().add_constraint(x_ge_4).add_constraint(x_lt_5).add_constraint(x_ge_3),
                    x_subst().add_constraint(x_ge_3).add_constraint(x_lt_4).add_constraint(x_lt_5),
                ],
            ),
        ),
        'splits': split_dicts(
            (11, [(6, x_ge_5), (7, mlAnd([x_ge_3, x_lt_5]))]),
            (1, [(4, mlAnd([x_ge_0, x_lt_3])), (5, x_lt_0), (10, mlOr([x_ge_5, mlAnd([x_ge_3, x_lt_5])]))]),
            csubst=x_subst(),
        ),
    }
    cfg = KCFG.from_dict(d)
    propagate_split_constraints(cfg)
    cfg.remove_node(2)
    cfg.remove_node(3)
    cfg.replace_node(KCFG.Node(6, CTerm(x_config(), [x_ge_5])))
    cfg.replace_node(KCFG.Node(7, CTerm(x_config(), [x_ge_3, x_lt_5])))
    cfg.replace_node(KCFG.Node(10, CTerm(x_config())))
    cfg.replace_node(KCFG.Node(11, CTerm(x_config())))
    return cfg


class EVMLikeSemantics(DefaultSemantics):
    def is_mergeable(self, ct1: CTerm, ct2: CTerm) -> bool:
        status_code_1 = ct1.cell('STATUSCODE_CELL')
        status_code_2 = ct2.cell('STATUSCODE_CELL')
        program_1 = ct1.cell('PROGRAM_CELL')
        program_2 = ct2.cell('PROGRAM_CELL')
        if type(status_code_1) is KApply and type(status_code_2) is KApply and type(program_1) is KToken and type(program_2) is KToken:
            return status_code_1 == status_code_2 and program_1 == program_2
        raise ValueError(f'Attempted to merge nodes with non-concrete <statusCode> or <program>: {(ct1, ct2)}')


MERGE_NODE_TEST_DATA: Final[tuple[tuple[KCFGSemantics, KCFG, KCFG], ...]] = (
    # (TestSemantics(), merge_node_test_kcfg(), merge_node_test_kcfg_simple_expected()),
    # (TestSemanticsIncomplete(), merge_node_test_kcfg(), merge_node_test_kcfg_incomplete_expected()),
    (EVMLikeSemantics(), KCFG.read_cfg_data(TEST_DATA_DIR / 'proof-files' / 'cse_f' / 'kcfg'), KCFG.read_cfg_data(TEST_DATA_DIR / 'proof-files' / 'cse_f' / 'expected_kcfg')),
)


@pytest.mark.parametrize('semantics, given_kcfg, expected_kcfg', MERGE_NODE_TEST_DATA, ids=count())
def test_merge_node(semantics: KCFGSemantics, given_kcfg: KCFG, expected_kcfg: KCFG):
    # When
    printer = KPrint(TEST_DATA_DIR / 'proof-files' / 'cse_f' / 'kdef' / 'kompiled')
    viewer = KCFGViewer(expected_kcfg, printer)
    viewer.run()
    # given_kcfg.merge_nodes(semantics)
    # # Then
    # assert given_kcfg.to_dict() == expected_kcfg.to_dict()
