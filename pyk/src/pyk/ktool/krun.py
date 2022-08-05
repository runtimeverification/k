import logging
from pathlib import Path
from subprocess import CalledProcessError, CompletedProcess
from tempfile import TemporaryDirectory
from typing import Final, List, Optional

from ..cli_utils import check_dir_path, check_file_path, run_process
from .kprint import KPrint

_LOGGER: Final = logging.getLogger(__name__)


def krun(
    input_file: Path,
    *,
    kompiled_dir: Optional[Path] = None,
) -> None:
    check_file_path(input_file)

    args = _build_arg_list(
        kompiled_dir=kompiled_dir,
    )

    try:
        _krun(str(input_file), *args)
    except CalledProcessError as err:
        raise RuntimeError(f'Command krun exited with code {err.returncode} for: {input_file}', err.stdout, err.stderr)


def _build_arg_list(
    *,
    kompiled_dir: Optional[Path],
) -> List[str]:
    args = []

    if kompiled_dir:
        args += ['--definition', str(kompiled_dir)]

    return args


def _krun(input_file: str, *args: str) -> CompletedProcess:
    run_args = ['krun', input_file] + list(args)
    return run_process(run_args, _LOGGER)


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
        # TODO: we should not have to supply main_file_name, it should be read
        with open(self.definition_dir / 'backend.txt', 'r') as ba:
            self.backend = ba.read()
        with open(self.definition_dir / 'mainModule.txt', 'r') as mm:
            self.main_module = mm.read()
