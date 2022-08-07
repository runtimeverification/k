import json
import logging
from pathlib import Path
from subprocess import CalledProcessError, CompletedProcess
from tempfile import NamedTemporaryFile, TemporaryDirectory
from typing import Final, List, Optional

from ..cli_utils import check_dir_path, check_file_path, run_process
from ..cterm import CTerm
from ..kast import KAst, KInner
from .kprint import KPrint

_LOGGER: Final = logging.getLogger(__name__)


def _krun(
    definition_dir: Path,
    input_file: Path,
    depth: Optional[int] = None,
    args: List[str] = [],
) -> CompletedProcess:
    check_file_path(input_file)

    krun_command = ['krun', '--definition', str(definition_dir), str(input_file)]

    if depth and depth >= 0:
        args += ['--depth', str(depth)]

    try:
        return run_process(krun_command + args, _LOGGER)
    except CalledProcessError as err:
        raise RuntimeError(f'Command krun exited with code {err.returncode} for: {input_file}', err.stdout, err.stderr)


class KRun(KPrint):

    backend: str
    main_module: str

    def __init__(self, definition_dir: Path, use_directory: Optional[Path] = None) -> None:
        super(KRun, self).__init__(definition_dir, use_directory=use_directory)
        if not use_directory:
            _temp_dir = TemporaryDirectory()
            self.use_directory = Path(_temp_dir.name)
        else:
            self.use_directory = Path(use_directory)
            check_dir_path(self.use_directory)
        with open(self.definition_dir / 'backend.txt', 'r') as ba:
            self.backend = ba.read()
        with open(self.definition_dir / 'mainModule.txt', 'r') as mm:
            self.main_module = mm.read()

    def run(self, init_PGM: KInner, depth: Optional[int] = None, args: List[str] = []) -> CTerm:
        with NamedTemporaryFile('w', dir=self.use_directory, delete=False) as ntf:
            ntf.write(self.pretty_print(init_PGM))
            ntf.flush()
            result = _krun(self.definition_dir, Path(ntf.name), depth=depth, args=['--output', 'json'])
            if result.returncode != 0:
                raise RuntimeError('Non-zero exit-code from krun.')
            result_kast = KAst.from_dict(json.loads(result.stdout)['term'])
            assert isinstance(result_kast, KInner)
            return CTerm(result_kast)
