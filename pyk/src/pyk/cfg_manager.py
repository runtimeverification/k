import json
import logging
import os
from pathlib import Path
from typing import Any, Dict, Final, Iterable, Optional

from .cli_utils import check_dir_path, check_file_path
from .cterm import CTerm
from .kast import KApply, KClaim, KDefinition, KInner, KNonTerminal, KVariable, Subst
from .kastManip import (
    abstract_term_safely,
    bool_to_ml_pred,
    bottom_up,
    count_vars,
    extract_lhs,
    extract_rhs,
    free_vars,
    split_config_from,
)
from .kcfg import KCFG

_LOGGER: Final = logging.getLogger(__name__)


def instantiate_cell_vars(definition: KDefinition, term: KInner) -> KInner:
    def _cell_vars_to_labels(_kast):
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

    return bottom_up(_cell_vars_to_labels, term)


def rename_generated_vars(cterm: CTerm) -> CTerm:
    state, *constraints = cterm
    _, config_subst = split_config_from(state)
    config_var_count = {cvar: count_vars(ccontents) for cvar, ccontents in config_subst.items()}
    vs = free_vars(cterm.kast)
    var_subst: Dict[str, KInner] = {}
    for v in vs:
        if v.startswith('_Gen') or v.startswith('?_Gen') or v.startswith('_DotVar') or v.startswith('?_DotVar'):
            cvars = [cv for cv in config_var_count if v in config_var_count[cv]]
            if len(cvars) > 1:
                raise ValueError(f'Found "Gen*" or "DotVar*" variable with multiple occurances: {v}')
            cvar = cvars[0]
            new_v = abstract_term_safely(KVariable(v), base_name=cvar)
            while new_v.name in vs:
                new_v = abstract_term_safely(KVariable(new_v.name), base_name=cvar)
            var_subst[v] = new_v
            vs.append(new_v.name)
    return CTerm(Subst(var_subst).apply(cterm.kast))


class CFGManager:
    summary_name: Final[str]
    strategy_name: Final[str]
    spec_file: Final[Path]
    main_file: Final[Optional[Path]]
    summary_dir: Final[Path]
    config_file: Final[Path]
    definition_dir: Final[Path]
    use_directory: Final[Path]
    cfg_file: Final[Path]
    cfg_json_file: Final[Path]
    cfg_ids_json_file: Final[Path]

    @staticmethod
    def create(
        *, summary_name: str, strategy_name: str, summary_dir: Path, spec_file: Path, main_file: Optional[Path]
    ) -> 'CFGManager':
        manager = CFGManager(
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
    def load(summary_dir: Path) -> 'CFGManager':
        config = None
        with open(summary_dir / 'config.json', 'r') as config_file:
            config = json.load(config_file)
        manager = CFGManager(
            summary_name=config['summaryName'],
            strategy_name=config['strategy_name'],
            summary_dir=summary_dir,
            spec_file=Path(config['specificationFile']),
            main_file=Path(config['verificationFile']) if config['verificationFile'] else None,
        )
        manager._check_paths()
        return manager

    def __init__(
        self, *, summary_name: str, strategy_name: str, summary_dir: Path, spec_file: Path, main_file: Optional[Path]
    ):
        self.summary_name = summary_name
        self.strategy_name = strategy_name
        self.spec_file = spec_file
        self.main_file = main_file
        self.summary_dir = summary_dir
        self.config_file = summary_dir / 'config.json'
        self.definition_dir = summary_dir / 'kompiled'
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

    def empty_cfg(self) -> KCFG:
        return KCFG()

    def cfg_from_claim(self, defn: KDefinition, claim: KClaim) -> KCFG:
        cfg = KCFG()
        claim_body = claim.body
        claim_body = instantiate_cell_vars(defn, claim_body)
        claim_body = rename_generated_vars(CTerm(claim_body)).kast

        claim_lhs = CTerm(extract_lhs(claim_body)).add_constraint(bool_to_ml_pred(claim.requires))
        init_state = cfg.create_node(claim_lhs)
        cfg.add_init(init_state.id)

        claim_rhs = CTerm(extract_rhs(claim_body)).add_constraint(bool_to_ml_pred(claim.ensures))
        target_state = cfg.create_node(claim_rhs)
        cfg.add_target(target_state.id)

        return cfg

    def list_cfgs(self) -> Iterable[str]:
        return self._read_cfgs().keys()

    def write_cfg(self, name: str, cfg: KCFG) -> None:
        dct = self._read_cfgs()
        dct[name] = cfg
        self._write_cfgs(dct)

    def read_cfg(self, name: str) -> KCFG:
        return self._read_cfgs()[name]

    def default_cfg_id(self) -> str:
        all_cfgs = self._read_cfgs()
        if len(all_cfgs) == 0:
            raise ValueError(f'No CFGs found in {self.cfg_file}.')
        if len(all_cfgs) > 1:
            raise ValueError(f'More than 1 CFG found in {self.cfg_file}, could not select default.')
        return list(all_cfgs.keys())[0]

    def _write_cfgs(self, cfgs: Dict[str, KCFG]) -> None:
        dct = {name: cfgs[name].to_dict() for name in cfgs}
        with open(self.cfg_ids_json_file, 'w+') as c_file:
            c_file.write(json.dumps(list(dct.keys()), sort_keys=True))
        with open(self.cfg_json_file, 'w') as c_file:
            c_file.write(json.dumps(dct, sort_keys=True))
            c_file.flush()
            _LOGGER.info('Wrote CFG: ' + str(self.cfg_json_file))

    def _read_cfgs(self) -> Dict[str, KCFG]:
        with open(self.cfg_json_file, 'r') as c_file:
            dct = json.loads(c_file.read())
            return {name: KCFG.from_dict(dct[name]) for name in dct}
