from __future__ import annotations

import sysconfig
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from typing import TYPE_CHECKING

from ..cli_utils import check_file_path

if TYPE_CHECKING:
    from types import ModuleType
    from typing import Final, Union

PYTHON_EXTENSION_SUFFIX: Final = sysconfig.get_config_var('EXT_SUFFIX')


def import_from_file(module_name: str, module_file: Union[str, Path]) -> ModuleType:
    module_file = Path(module_file).resolve()
    check_file_path(module_file)

    spec = spec_from_file_location(module_name, module_file)
    if not spec:
        raise ValueError('Could not create ModuleSpec')

    module = module_from_spec(spec)
    if not module:
        raise ValueError('Could not create ModuleType')

    if not spec.loader:
        raise ValueError('Spec has no loader')

    spec.loader.exec_module(module)

    return module
