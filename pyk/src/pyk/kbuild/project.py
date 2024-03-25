from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import cached_property
from importlib import resources
from pathlib import Path, PosixPath
from typing import TYPE_CHECKING, final

import tomli

from ..cli.utils import relative_path
from ..utils import FrozenDict, abs_or_rel_to, check_dir_path, check_file_path, check_relative_path, single
from .config import PROJECT_FILE_NAME

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from typing import Any


class Source(ABC):
    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> Source:
        if 'path' in dct:
            return PathSource(Path(dct['path']))
        if 'package' in dct:
            return PackageSource(dct['package'])
        raise ValueError(f'Cannot parse source: {dct}')

    @abstractmethod
    def resolve(self, project_path: Path) -> Path: ...


@final
@dataclass(frozen=True)
class PathSource(Source):
    path: Path

    def resolve(self, project_path: Path) -> Path:
        return abs_or_rel_to(self.path, project_path)


@final
@dataclass(frozen=True)
class PackageSource(Source):
    package: str

    def resolve(self, project_path: Path) -> Path:
        traversable = resources.files(self.package)
        if not isinstance(traversable, PosixPath):
            raise ValueError(f'Package name {self.package!r} does not resolve to a directory')
        return traversable.resolve(strict=True)


@final
@dataclass(frozen=True)
class Target:
    name: str  # TODO Maybe remove name and store in project as Dict

    args: dict[str, Any]

    def __init__(
        self,
        *,
        name: str,
        args: Mapping[str, Any],
    ):
        if args['main-file']:
            main_file = Path(args['main-file'])
            check_relative_path(main_file)
        newargs = {key.replace('-', '_'): value for key, value in args.items()}
        newargs['main_file'] = main_file
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'args', newargs)


@final
@dataclass(frozen=True)
class Project:
    path: Path
    name: str
    version: str
    source_dir: Path
    resources: FrozenDict[str, Path]
    dependencies: tuple[Project, ...]
    targets: tuple[Target, ...]

    def __init__(
        self,
        *,
        path: str | Path,
        name: str,
        version: str,
        source_dir: str | Path,
        resources: Mapping[str, str | Path] | None = None,
        dependencies: Iterable[Project] = (),
        targets: Iterable[Target] = (),
    ):
        path = Path(path).resolve()
        check_dir_path(path)

        source_dir = path / relative_path(source_dir)
        check_dir_path(source_dir)

        resources = resources or {}
        resources = {
            resource_name: path / relative_path(resource_dir) for resource_name, resource_dir in resources.items()
        }

        object.__setattr__(self, 'path', path)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'version', version)
        object.__setattr__(self, 'source_dir', source_dir)
        object.__setattr__(self, 'resources', FrozenDict(resources))
        object.__setattr__(self, 'dependencies', tuple(dependencies))
        object.__setattr__(self, 'targets', tuple(targets))

    @staticmethod
    def load(project_file: str | Path) -> Project:
        project_file = Path(project_file)
        check_file_path(project_file)
        project_path = project_file.parent

        def _load_dependency(name: str, dct: Any) -> Project:
            source = Source.from_dict(dct)
            dependency_path = source.resolve(project_path)
            project = Project.load_from_dir(dependency_path)
            if project.name != name:
                raise ValueError(f'Invalid dependency, expected name {name}, got: {project.name}')
            return project

        with open(project_file, 'rb') as f:
            dct = tomli.load(f)

        project = Project(
            path=project_path,
            name=dct['project']['name'],
            version=dct['project']['version'],
            source_dir=dct['project']['source'],
            resources=dct['project'].get('resources'),
            dependencies=tuple(
                _load_dependency(name, source_dct) for name, source_dct in dct.get('dependencies', {}).items()
            ),
            targets=tuple(Target(name=name, args=target) for name, target in dct.get('targets', {}).items()),
        )

        return project

    @staticmethod
    def load_from_dir(project_dir: str | Path) -> Project:
        project_dir = Path(project_dir)
        check_dir_path(project_dir)
        return Project.load(project_dir / PROJECT_FILE_NAME)

    @cached_property
    def sub_projects(self) -> tuple[Project, ...]:
        res: tuple[Project, ...] = (self,)
        for project in self.dependencies:
            res += project.sub_projects
        return res

    @property
    def project_file(self) -> Path:
        return self.path / PROJECT_FILE_NAME

    @property
    def source_files(self) -> list[Path]:
        res: list[Path] = []
        res.extend(self.source_dir.rglob('*.k'))
        res.extend(self.source_dir.rglob('*.md'))
        return res

    @property
    def source_file_names(self) -> list[str]:
        return [str(source_file.relative_to(self.source_dir)) for source_file in self.source_files]

    @property
    def resource_files(self) -> dict[str, list[Path]]:
        res: dict[str, list[Path]] = {}
        for resource_name, resource_dir in self.resources.items():
            check_dir_path(resource_dir)
            res[resource_name] = [resource_file for resource_file in resource_dir.rglob('*') if resource_file.is_file()]
        return res

    @property
    def resource_file_names(self) -> dict[str, list[str]]:
        return {
            resource_name: [
                str(resource_file.relative_to(self.resources[resource_name])) for resource_file in resource_files
            ]
            for resource_name, resource_files in self.resource_files.items()
        }

    @property
    def all_files(self) -> list[Path]:
        res: list[Path] = []
        for sub_project in self.sub_projects:
            res.append(sub_project.project_file)
            res.extend(sub_project.source_files)
            for resource_name in sub_project.resources:
                res.extend(sub_project.resource_files[resource_name])
        return res

    def get_target(self, target_name: str) -> Target:
        # TODO Should be enforced as a validation rule
        return single(target for target in self.targets if target.name == target_name)
