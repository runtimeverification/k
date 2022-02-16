from itertools import chain
from pathlib import Path
from typing import Collection, Iterable, List, Optional, Tuple, cast

from pyk.cli_utils import check_dir_path, check_file_path
from pyk.cterm import CTerm
from pyk.kast import (
    TRUE,
    KApply,
    KClaim,
    KInner,
    KRewrite,
    KRule,
    KRuleLike,
    KVariable,
    Subst,
    flattenLabel,
)
from pyk.kastManip import (
    bool_to_ml_pred,
    count_vars,
    extract_lhs,
    extract_rhs,
    ml_pred_to_bool,
    push_down_rewrites,
    remove_generated_cells,
    simplifyBool,
)
from pyk.kcfg import KCFG
from pyk.ktool import KProve, paren
from pyk.prelude import Sorts, mlAnd, mlTop

from .utils import count_rhs_vars, drop_var_prefixes


class CfgProver:
    cfg: KCFG
    kprove: KProve
    max_depth: int

    def __init__(
        self,
        cfg: KCFG,
        kompiled_dir: Path,
        main_file: Path,
        *,
        prover_dir: Optional[Path] = None,
        include_dirs: Optional[Collection[Path]] = None,  # Other than main_file.parent and kompiled_dir.parent, which are implied
        max_depth: Optional[int] = None,
    ) -> None:
        # TODO docstring
        include_dirs = include_dirs or []
        self.max_depth = max_depth if max_depth is not None else 1000
        self.cfg = cfg

        check_dir_path(kompiled_dir)
        check_file_path(main_file)
        if prover_dir:
            check_dir_path(prover_dir)
        for include_dir in include_dirs:
            check_dir_path(include_dir)

        main_file_name = main_file.name
        self.includes = [str(include_dir) for include_dir in include_dirs] + [str(main_file.parent)]

        self.kprove = KProve(
            kompiled_directory=kompiled_dir,
            main_file_name=main_file_name,
            use_directory=str(prover_dir)
        )

        # TODO eliminate hack: patch symbol table
        self.kprove.symbol_table['_+Int_'] = paren(self.kprove.symbol_table['_+Int_'])

    def expand(self, node_id: str) -> List[str]:
        self._check_frontier(node_id)

        node = self.cfg.node(node_id)
        target = list(self.cfg.target)[0]  # TODO multiple targets?

        claim = cast(KClaim, cterms_to_rule(node.cterm, target.cterm, claim=True))  # TODO eliminate cast
        child_terms = self._prove_no_branching(claim, f'expand-{node.id}')

        if len(child_terms) == 1:
            child_term = child_terms[0]
            assert child_term == mlTop()
            self.cfg.create_edge(node.id, target.id, TRUE, 1)
            self.cfg.add_expanded(node.id)
            return []

        child_node_ids = []
        for child_term in child_terms:
            child_term = remove_generated_cells(child_term)
            child_term = drop_var_prefixes(child_term)  # TODO clean-up inside CTerm
            child_cterm = CTerm(child_term)
            child_node = self.cfg.create_node(child_cterm)
            self.cfg.create_edge(node.id, child_node.id, TRUE, 1)
            child_node_ids.append(child_node.id)
        self.cfg.add_expanded(node.id)

        return child_node_ids

    def cover(self, node_id, coverer_ids: Optional[Iterable[str]] = None, semantic=False) -> Optional[Tuple[str, Subst]]:
        node = self.cfg.node(node_id)

        def except_node(nodes: Iterable[KCFG.Node]) -> Iterable[KCFG.Node]:
            return (other for other in nodes if other.id != node.id)

        coverers = except_node(map(self.cfg.node, coverer_ids) if coverer_ids is not None else self.cfg.nodes)  # TODO is covering by covered nodes sound?
        for coverer in coverers:
            subst = self.check_cover(node.id, coverer.id, semantic=semantic)
            if subst is not None:
                self.cfg.create_cover(node.id, coverer.id)
                return coverer.id, subst

        return None

    # TODO kore-match-disjunctions
    def check_cover(self, coveree_id: str, coverer_id: str, *, semantic=False) -> Optional[Subst]:
        coveree = self.cfg.node(coveree_id)
        coverer = self.cfg.node(coverer_id)

        if coveree.id == coverer.id:
            raise ValueError(f'Erroneous attempt to cover node by itself: {coveree.id}')

        match_res = coverer.cterm.match_with_constraint(coveree.cterm)

        if not match_res:
            return None

        subst, constraint = match_res

        if constraint == mlTop(Sorts.GENERATED_TOP_CELL):
            return subst

        if not semantic:
            return None

        claim: KClaim  # TODO ensure taking a step

        if type(constraint) == KApply and constraint.label.name == '#Implies':
            antecedent, consequent = constraint.args
            requires = simplifyBool(ml_pred_to_bool(antecedent))
            ensures = simplifyBool(ml_pred_to_bool(consequent))
            claim = KClaim(TRUE, requires=requires, ensures=ensures)
        else:
            claim = KClaim(TRUE, ensures=constraint)

        prove_res = self._prove(claim, f'cover-{coveree.id}-{coverer.id}', allow_zero_step=True)
        if prove_res == mlTop():
            return subst

        return None

    def write_cfg(self, cfg_path: Path) -> None:
        with open(cfg_path, 'w') as f:
            f.write(self.cfg.to_json())

    def cfg_dot(self) -> str:
        return self.cfg.to_dot(self.kprove)

    def _check_frontier(self, node_id: str) -> None:
        if not self.cfg.is_frontier(node_id):
            raise ValueError(f'CFG node is not on frontier: {node_id}')

    def _prove(self, claim: KClaim, spec_id: str, *, allow_zero_step=False) -> KInner:
        args = self._kprove_args()
        return self.kprove.prove_claim(claim, spec_id, allow_zero_step=allow_zero_step, args=args)

    def _prove_no_branching(self, claim: KClaim, spec_id: str) -> List[KInner]:
        args = self._kprove_args()
        args += ['--depth', str(self.max_depth)]
        args += ['--branching-allowed', '1']
        next_state = self.kprove.prove_claim(claim, spec_id, args=args)
        return flattenLabel('#Or', next_state)

    def _kprove_args(self) -> List[str]:
        return list(chain.from_iterable(['-I', include] for include in self.includes))


def cterms_from_rule(rule: KRuleLike) -> Tuple[CTerm, CTerm]:
    body = drop_var_prefixes(rule.body)
    lhs = extract_lhs(body)
    rhs = extract_rhs(body)
    requires = drop_var_prefixes(rule.requires)
    ensures = drop_var_prefixes(rule.ensures)
    return CTerm(mlAnd([lhs, bool_to_ml_pred(requires)])), CTerm(mlAnd([rhs, bool_to_ml_pred(ensures)]))


def cterms_to_rule(source: CTerm, target: CTerm, path_constraints: Iterable[KInner] = [], *, claim=False) -> KRuleLike:
    lhs_constraints = set(chain(source.constraints, path_constraints))
    rhs_constraints = set(c for c in target.constraints if c not in lhs_constraints)

    body = push_down_rewrites(KRewrite(source.config, target.config))
    requires = simplifyBool(ml_pred_to_bool(mlAnd(lhs_constraints)))
    ensures = simplifyBool(ml_pred_to_bool(mlAnd(rhs_constraints)))

    var_count = count_vars(body) + count_vars(requires) + count_vars(ensures)
    rhs_var_count = count_rhs_vars(body) + count_vars(ensures)

    singletons = {k for k, v in var_count.items() if v == 1}
    existentials = {k for k, v in rhs_var_count.items() if var_count[k] <= v}

    subst_items = ((k, '_' + k) for k in singletons)
    subst_items = ((k, ('?' if k in existentials else '') + v) for k, v in subst_items)
    subst_dict = {k: KVariable(v) for k, v in subst_items}
    subst = Subst(subst_dict)

    body = subst(body)
    requires = subst(requires)
    ensures = subst(ensures)

    if claim:
        return KClaim(body=body, requires=requires, ensures=ensures)

    return KRule(body=body, requires=requires, ensures=ensures)
