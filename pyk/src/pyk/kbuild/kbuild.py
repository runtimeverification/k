import shutil
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from typing import List, Union, final

from ..ktool.kompile import kompile
from .package import Package
from .utils import k_version, sync_files


@final
@dataclass(frozen=True)
class KBuild:
    kbuild_dir: Path

    def __init__(self, kbuild_dir: Union[str, Path]):
        kbuild_dir = Path(kbuild_dir).resolve()
        object.__setattr__(self, 'kbuild_dir', kbuild_dir)

    @cached_property
    def k_version(self) -> str:
        return k_version().text

    def sync(self, package: Package) -> List[Path]:
        return sync_files(
            source_dir=package.project.source_dir,
            target_dir=self.kbuild_dir / package.include_dir / package.name,
            file_names=package.project.include_file_names,
        )

    def definition_dir(self, package: Package, target_name: str) -> Path:
        return self.kbuild_dir / package.target_dir / self.k_version / target_name

    def clean(self, package: Package, target_name: str) -> None:
        shutil.rmtree(self.definition_dir(package, target_name), ignore_errors=True)

    def kompile(self, package: Package, target_name: str) -> Path:
        for sub_package in package.sub_packages:
            self.sync(sub_package)

        output_dir = self.definition_dir(package, target_name)

        if self.up_to_date(package, target_name):
            return output_dir

        target = package.project.get_target(target_name)
        kompile(
            output_dir=output_dir,
            include_dirs=[self.kbuild_dir / include_dir for include_dir in package.include_dirs],
            cwd=self.kbuild_dir / package.include_dir / package.name,
            **target.kompile_args(),
        )

        return output_dir

    def up_to_date(self, package: Package, target_name: str) -> bool:
        definition_dir = self.definition_dir(package, target_name)
        timestamp = definition_dir / 'timestamp'

        if not timestamp.exists():
            return False

        input_files: List[Path] = []
        for sub_package in package.sub_packages:
            input_files.append(sub_package.project.project_file)
            input_files.extend(self.kbuild_dir / include_file for include_file in sub_package.include_files)

        input_timestamps = (input_file.stat().st_mtime for input_file in input_files)
        target_timestamp = timestamp.stat().st_mtime
        return all(input_timestamp < target_timestamp for input_timestamp in input_timestamps)
