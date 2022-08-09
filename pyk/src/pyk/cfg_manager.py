import json
import logging
import os
from pathlib import Path
from typing import Any, Dict, Final, Iterable, Optional, Tuple

from .cli_utils import check_dir_path, check_file_path
from .cterm import CTerm, split_config_and_constraints
from .kast import (
    KApply,
    KClaim,
    KDefinition,
    KInner,
    KNonTerminal,
    KRewrite,
    KVariable,
    Subst,
)
from .kastManip import (
    abstract_term_safely,
    bool_to_ml_pred,
    bottom_up,
    collectFreeVars,
    count_vars,
    extract_lhs,
    extract_rhs,
    flatten_label,
    getCell,
    minimize_term,
    ml_pred_to_bool,
    push_down_rewrites,
    remove_generated_cells,
    splitConfigFrom,
    substitute,
)
from .kcfg import KCFG
from .ktool.kprint import KPrint
from .prelude import Bool, Sorts, mlAnd, mlBottom, mlTop

_LOGGER: Final = logging.getLogger(__name__)


def check_implication(kprint: KPrint, concrete: CTerm, abstract: CTerm) -> Tuple[bool, str]:

    def _no_cell_rewrite_to_dots(term: KInner) -> KInner:
        def _no_cell_rewrite_to_dots(_term: KInner):
            if type(_term) is KApply and _term.is_cell:
                lhs = extract_lhs(_term)
                rhs = extract_rhs(_term)
                if lhs == rhs:
                    return KApply(_term.label, [abstract_term_safely(lhs, base_name=_term.label.name)])
            return _term
        return bottom_up(_no_cell_rewrite_to_dots, term)

    def _is_cell_subst(csubst: KInner) -> bool:
        if type(csubst) is KApply and csubst.label.name == '_==K_':
            csubst_arg = csubst.args[0]
            if type(csubst_arg) is KVariable and csubst_arg.name.endswith('_CELL'):
                return True
        return False

    def _is_negative_cell_subst(constraint: KInner) -> bool:
        constraint_bool = ml_pred_to_bool(constraint)
        if type(constraint_bool) is KApply and constraint_bool.label.name == 'notBool_':
            negative_constraint = constraint_bool.args[0]
            if type(negative_constraint) is KApply and negative_constraint.label.name == '_andBool_':
                constraints = flatten_label('_andBool_', negative_constraint)
                cell_constraints = list(filter(_is_cell_subst, constraints))
                if len(cell_constraints) > 0:
                    return True
        return False

    concrete_config, *concrete_constraints = concrete
    abstract_config, *abstract_constraints = abstract
    config_match = abstract_config.match(concrete_config)
    if config_match is None:
        _, concrete_subst = splitConfigFrom(concrete_config)
        cell_names = concrete_subst.keys()
        failing_cells = []
        for cell in cell_names:
            concrete_cell = getCell(concrete_config, cell)
            abstract_cell = getCell(abstract_config, cell)
            cell_match = abstract_cell.match(concrete_cell)
            if cell_match is None:
                failing_cell = push_down_rewrites(KRewrite(concrete_cell, abstract_cell))
                failing_cell = _no_cell_rewrite_to_dots(failing_cell)
                failing_cells.append((cell, failing_cell))
            else:
                abstract_config = cell_match.apply(abstract_config)
        failing_cells_str = '\n'.join(f'{cell}: {kprint.pretty_print(minimize_term(rew))}' for cell, rew in failing_cells)
        return (False, f'Structural matching failed, the following cells failed individually (abstract => concrete):\n{failing_cells_str}')
    else:
        abstract_constraints = [config_match.apply(abstract_constraint) for abstract_constraint in abstract_constraints]
        abstract_constraints = list(filter(lambda x: not CTerm._is_spurious_constraint(x), [config_match.apply(abstract_constraint) for abstract_constraint in abstract_constraints]))
        impl = CTerm._ml_impl(concrete_constraints, abstract_constraints)
        if impl != mlTop(Sorts.GENERATED_TOP_CELL):
            fail_str = kprint.pretty_print(impl)
            negative_cell_constraints = list(filter(_is_negative_cell_subst, concrete_constraints))
            if len(negative_cell_constraints) > 0:
                fail_str = f'{fail_str}\n\nNegated cell substitutions found (consider using _ => ?_):\n' + '\n'.join([kprint.pretty_print(cc) for cc in negative_cell_constraints])
            return (False, f'Implication check failed, the following is the remaining implication:\n{fail_str}')
    return (True, '')


def instantiate_cell_vars(definition: KDefinition, term: KInner) -> KInner:
    def _cellVarsToLabels(_kast):
        if type(_kast) is KApply and _kast.is_cell:
            production = definition.production_for_klabel(_kast.label)
            production_arity = [prod_item.sort for prod_item in production.items if type(prod_item) is KNonTerminal]
            new_args = []
            for sort, arg in zip(production_arity, _kast.args):
                if sort.name.endswith('Cell') and type(arg) is KVariable:
                    new_args.append(definition.empty_config(sort))
                else:
                    new_args.append(arg)
            return KApply(_kast.label, new_args)
        return _kast
    return bottom_up(_cellVarsToLabels, term)


def rename_generated_vars(cterm: CTerm) -> CTerm:
    state, *constraints = cterm
    _, config_subst = splitConfigFrom(state)
    config_var_count = {cvar: count_vars(ccontents) for cvar, ccontents in config_subst.items()}
    free_vars = collectFreeVars(cterm.term)
    var_subst: Dict[str, KInner] = {}
    for v in free_vars:
        if v.startswith('_Gen') or v.startswith('?_Gen') or v.startswith('_DotVar') or v.startswith('?_DotVar'):
            cvars = [cv for cv in config_var_count if v in config_var_count[cv]]
            if len(cvars) > 1:
                raise ValueError(f'Found "Gen*" or "DotVar*" variable with multiple occurances: {v}')
            cvar = cvars[0]
            new_v = abstract_term_safely(KVariable(v), base_name=cvar)
            while new_v.name in free_vars:
                new_v = abstract_term_safely(KVariable(new_v.name), base_name=cvar)
            var_subst[v] = new_v
            free_vars.append(new_v.name)
    return CTerm(Subst(var_subst).apply(cterm.term))


def sanitize_config(defn: KDefinition, init_term: KInner) -> KInner:

    def _var_name(vname):
        new_vname = vname
        while new_vname.startswith('_') or new_vname.startswith('?'):
            new_vname = new_vname[1:]
        return new_vname

    free_vars_subst = {vname: KVariable(_var_name(vname)) for vname in collectFreeVars(init_term)}

    # TODO: This is somewhat hacky. We shouldn't have to touch the config this much.
    # Likely, the frontend should just be giving us initial states with these already in place.
    def _remove_cell_map_definedness(_kast):
        if type(_kast) is KApply:
            if _kast.label.name.endswith('CellMap:in_keys'):
                return Bool.false
            elif _kast.label.name.endswith('CellMapItem'):
                return _kast.args[1]
        return _kast

    new_term = substitute(init_term, free_vars_subst)
    new_term = remove_generated_cells(new_term)
    new_term = bottom_up(_remove_cell_map_definedness, new_term)

    if new_term not in [mlTop(), mlBottom()]:
        config, constraint = split_config_and_constraints(new_term)
        constraints = [bool_to_ml_pred(ml_pred_to_bool(c, unsafe=True)) for c in flatten_label('#And', constraint)]
        new_term = mlAnd([config] + constraints)

    return new_term


class SummaryManager:
    summary_name: Final[str]
    strategy_name: Final[str]
    spec_file: Final[Path]
    main_file: Final[Optional[Path]]
    summary_dir: Final[Path]
    config_file: Final[Path]
    kompiled_dir: Final[Path]
    use_directory: Final[Path]
    cfg_file: Final[Path]
    cfg_json_file: Final[Path]
    cfg_ids_json_file: Final[Path]

    @staticmethod
    def create(*, summary_name: str, strategy_name: str, summary_dir: Path, spec_file: Path, main_file: Optional[Path]) -> 'SummaryManager':
        manager = SummaryManager(
            summary_name=summary_name,
            strategy_name=strategy_name,
            summary_dir=summary_dir,
            spec_file=spec_file,
            main_file=Path(main_file) if main_file else None,
        )
        os.makedirs(manager.use_directory, exist_ok=True)
        with open(manager.config_file, 'w+') as config_file:
            json.dump(manager.config(), config_file, indent=2)
        _LOGGER.info('Wrote Summary: ' + str(manager.config_file))
        manager._check_paths()
        return manager

    @staticmethod
    def load(summary_dir: Path) -> 'SummaryManager':
        config = None
        with open(summary_dir / 'config.json', 'r') as config_file:
            config = json.load(config_file)
        manager = SummaryManager(
            summary_name=config['summaryName'],
            strategy_name=config['strategy_name'],
            summary_dir=summary_dir,
            spec_file=Path(config['specificationFile']),
            main_file=Path(config['verificationFile']) if config['verificationFile'] else None
        )
        manager._check_paths()
        return manager

    def __init__(self, *, summary_name: str, strategy_name: str, summary_dir: Path, spec_file: Path, main_file: Optional[Path]):
        self.summary_name = summary_name
        self.strategy_name = strategy_name
        self.spec_file = spec_file
        self.main_file = main_file
        self.summary_dir = summary_dir
        self.config_file = summary_dir / 'config.json'
        self.kompiled_dir = summary_dir / 'kompiled'
        self.use_directory = summary_dir / 'blobs'
        self.cfg_file = self.use_directory / 'cfg'
        self.cfg_json_file = self.cfg_file.with_suffix('.json')
        self.cfg_ids_json_file = self.use_directory / 'cfg_ids.json'

    def _check_paths(self) -> None:
        check_file_path(self.spec_file)
        if self.main_file:
            check_file_path(self.main_file)
        check_file_path(self.config_file)
        check_dir_path(self.use_directory)

    def config(self) -> Dict[str, Any]:
        return {
            # Used by KIT
            # -----------
            "specificationFile": str(self.spec_file),

            # Used by KSummarize
            # ------------------
            "verificationFile": str(self.main_file) if self.main_file else None,
            "strategy_name": self.strategy_name,

            # Used by the web interface
            # -------------------------
            # TODO: These should be managed by the web interface, though we
            # should allow reading/writing this file without modifying these fields.
            "summaryName": self.summary_name,
            "id": self.summary_name.replace('/', '-'),
            "summaryDirectory": str(self.summary_dir),  # TODO: Is this really needed?
            "states": [],
            "runningProcesses": 0,
            "totalProcesses": 0,
        }

    def emptyCFG(self) -> KCFG:
        return KCFG()

    def cfg_from_claim(self, defn: KDefinition, claim: KClaim) -> KCFG:
        cfg = KCFG()
        claim_body = claim.body
        claim_body = instantiate_cell_vars(defn, claim_body)
        claim_body = rename_generated_vars(CTerm(claim_body)).term

        claim_lhs = extract_lhs(claim_body)
        claim_lhs = claim_lhs if claim.requires == Bool.true else mlAnd([claim_lhs, bool_to_ml_pred(claim.requires)])
        claim_lhs_cterm = CTerm(sanitize_config(defn, claim_lhs))
        init_state = cfg.create_node(claim_lhs_cterm)
        cfg.add_init(init_state.id)

        claim_rhs = extract_rhs(claim_body)
        claim_rhs = claim_rhs if claim.ensures == Bool.true else mlAnd([claim_rhs, bool_to_ml_pred(claim.ensures)])
        claim_rhs_cterm = CTerm(sanitize_config(defn, claim_rhs))
        target_state = cfg.create_node(claim_rhs_cterm)
        cfg.add_target(target_state.id)

        return cfg

    def listCFGs(self) -> Iterable[str]:
        return self._readCFGs().keys()

    def writeCFG(self, name: str, cfg: KCFG) -> None:
        dct = self._readCFGs()
        dct[name] = cfg
        self._writeCFGs(dct)

    def readCFG(self, name: str) -> KCFG:
        return self._readCFGs()[name]

    def _readCFGs(self) -> Dict[str, KCFG]:
        with open(self.cfg_json_file, 'r') as c_file:
            dct = json.loads(c_file.read())
            return {name: KCFG.from_dict(dct[name]) for name in dct}

    def _writeCFGs(self, cfgs: Dict[str, KCFG]) -> None:
        dct = {name: cfgs[name].to_dict() for name in cfgs}
        with open(self.cfg_ids_json_file, 'w+') as c_file:
            c_file.write(json.dumps(list(dct.keys()), sort_keys=True))
        with open(self.cfg_json_file, 'w') as c_file:
            c_file.write(json.dumps(dct, sort_keys=True))
            c_file.flush()
            _LOGGER.info('Wrote CFG: ' + str(self.cfg_json_file))

    def default_cfg_id(self) -> str:
        all_cfgs = self._readCFGs()
        if len(all_cfgs) == 0:
            raise ValueError(f'No CFGs found in {self.cfg_file}.')
        if len(all_cfgs) > 1:
            raise ValueError(f'More than 1 CFG found in {self.cfg_file}, could not select default.')
        return list(all_cfgs.keys())[0]
