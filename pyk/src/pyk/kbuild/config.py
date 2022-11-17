import os
from pathlib import Path
from typing import Final

PROJECT_FILE_NAME: Final = 'kbuild.toml'
KBUILD_DIR_NAME: Final = '.kbuild'

KBUILD_DIR_ENV: Final = os.getenv('KBUILD_DIR')
KBUILD_DIR: Final = Path(KBUILD_DIR_ENV) if KBUILD_DIR_ENV else Path.home() / KBUILD_DIR_NAME
