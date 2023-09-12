from __future__ import annotations

import re
import shutil
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from typing import TYPE_CHECKING, final

from filelock import FileLock

from ..ktool.kompile import kompile
from ..utils import single
from .utils import k_version, sync_files

if TYPE_CHECKING:
    from re import Match
    from typing import Any

    from .package import Package
    from .project import Target


@final
@dataclass(frozen=True)
class KBuild:
    kdist_dir: Path

    def __init__(self, kdist_dir: str | Path):
        kdist_dir = Path(kdist_dir).resolve()
        object.__setattr__(self, 'kdist_dir', kdist_dir)

    @cached_property
    def k_version(self) -> str:
        return k_version().text

    def definition_dir(self, package: Package, target_name: str) -> Path:
        return self.kdist_dir / package.target_dir / self.k_version / target_name

    def resource_dir(self, package: Package, resource_name: str) -> Path:
        return self.kdist_dir / package.resource_dir / resource_name

    def resource_files(self, package: Package, resource_name: str) -> list[Path]:
        return [
            self.resource_dir(package, resource_name) / file_name
            for file_name in package.project.resource_file_names[resource_name]
        ]

    def include_dir(self, package: Package) -> Path:
        return self.kdist_dir / package.include_dir

    def source_dir(self, package: Package) -> Path:
        return self.include_dir(package) / package.name

    def source_files(self, package: Package) -> list[Path]:
        return [self.source_dir(package) / file_name for file_name in package.project.source_file_names]

    def clean(self, package: Package, target_name: str) -> None:
        shutil.rmtree(self.definition_dir(package, target_name), ignore_errors=True)

    def sync(self, package: Package) -> list[Path]:
        res: list[Path] = []

        # Sync sources
        res += sync_files(
            source_dir=package.project.source_dir,
            target_dir=self.source_dir(package),
            file_names=package.project.source_file_names,
        )

        # Sync resources
        for resource_name in package.project.resources:
            res += sync_files(
                source_dir=package.project.resources[resource_name],
                target_dir=self.resource_dir(package, resource_name),
                file_names=package.project.resource_file_names[resource_name],
            )

        return res

    def kompile(self, package: Package, target_name: str) -> Path:
        self.kdist_dir.mkdir(parents=True, exist_ok=True)
        with FileLock(self.kdist_dir / '.lock'):
            for sub_package in package.sub_packages:
                self.sync(sub_package)

            output_dir = self.definition_dir(package, target_name)

            if self.up_to_date(package, target_name):
                return output_dir

            target = package.project.get_target(target_name)
            args = self.kompile_args(package, target)
            kompile(
                output_dir=output_dir,
                include_dirs=[self.include_dir(sub_package) for sub_package in package.sub_packages],
                cwd=self.kdist_dir,
                **args,
            )

            return output_dir

    def up_to_date(self, package: Package, target_name: str) -> bool:
        definition_dir = self.definition_dir(package, target_name)
        timestamp = definition_dir / 'timestamp'

        if not timestamp.exists():
            return False

        input_files: list[Path] = []
        for sub_package in package.sub_packages:
            input_files.append(sub_package.project.project_file)
            input_files.extend(self.source_files(sub_package))
            for resource_name in sub_package.project.resources:
                input_files.extend(self.resource_files(sub_package, resource_name))

        input_timestamps = (input_file.stat().st_mtime for input_file in input_files)
        target_timestamp = timestamp.stat().st_mtime
        return all(input_timestamp < target_timestamp for input_timestamp in input_timestamps)

    def kompile_args(self, package: Package, target: Target) -> dict[str, Any]:
        args = target.dict
        args.pop('name')
        args['main_file'] = self.source_dir(package) / args['main_file']

        if 'ccopts' in args:
            args['ccopts'] = [self.render_opt(package, opt) for opt in args['ccopts']]

        return args

    def render_opt(self, package: Package, opt: str) -> str:
        def render(match: Match) -> str:
            package_name = match.group('package')
            resource_name = match.group('resource')

            sub_package = single(
                sub_package for sub_package in package.sub_packages if sub_package.name == package_name
            )
            resource_path = self.resource_dir(sub_package, resource_name).resolve()

            if not resource_path.exists():
                raise ValueError('Failed to resolve opt {opt}: resource path {resource_path} does not exist')

            return str(resource_path)

        pattern = re.compile(r'{{ *(?P<package>\S+):(?P<resource>\S+) *}}')
        return pattern.sub(render, opt)
