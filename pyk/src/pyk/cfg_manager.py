import json
import logging
import os
from pathlib import Path
from typing import Any, Dict, Final, Iterable, Optional

from .cli_utils import check_dir_path, check_file_path
from .kast.outer import KClaim, KDefinition
from .kcfg import KCFG

_LOGGER: Final = logging.getLogger(__name__)


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
            'specificationFile': str(self.spec_file),
            # Used by KSummarize
            # ------------------
            'verificationFile': str(self.main_file) if self.main_file else None,
            'strategy_name': self.strategy_name,
            # Used by the web interface
            # -------------------------
            # TODO: These should be managed by the web interface, though we
            # should allow reading/writing this file without modifying these fields.
            'summaryName': self.summary_name,
            'id': self.summary_name.replace('/', '-'),
            'summaryDirectory': str(self.summary_dir),  # TODO: Is this really needed?
            'states': [],
            'runningProcesses': 0,
            'totalProcesses': 0,
        }

    def empty_cfg(self) -> KCFG:
        return KCFG()

    def cfg_from_claim(self, defn: KDefinition, claim: KClaim) -> KCFG:
        return KCFG.from_claim(defn, claim)

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
