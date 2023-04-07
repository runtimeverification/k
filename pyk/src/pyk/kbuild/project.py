from __future__ import annotations

import dataclasses
from abc import ABC
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, final

import tomli

from ..cli_utils import (
    abs_or_rel_to,
    check_absolute_path,
    check_dir_path,
    check_file_path,
    check_relative_path,
    relative_path,
)
from ..ktool.kompile import KompileBackend
from ..utils import FrozenDict, single
from .config import PROJECT_FILE_NAME

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from typing import Any


class Source(ABC):  # noqa: B024
    @staticmethod
    def from_dict(project_dir: Path, dct: Mapping[str, Any]) -> Source:
        if 'path' in dct:
            return PathSource.from_dict(project_dir, dct)

        if 'git' in dct:
            return GitSource(git=dct['git'], rev=dct['rev'])

        raise ValueError(f'Invalid source: {dct}')


@final
@dataclass(frozen=True)
class PathSource(Source):
    path: Path

    def __init__(self, path: Path):
        check_dir_path(path)
        check_absolute_path(path)
        check_file_path(path / PROJECT_FILE_NAME)
        path = path.resolve()
        object.__setattr__(self, 'path', path)

    @staticmethod
    def from_dict(project_dir: Path, dct: Mapping[str, Any]) -> PathSource:
        path = abs_or_rel_to(Path(dct['path']), project_dir).resolve()
        return PathSource(path=path)


@final
@dataclass(frozen=True)
class GitSource(Source):
    git: str
    rev: str


@final
@dataclass(frozen=True)
class Dependency:  # TODO Maybe eliminate and store in project as Dict
    name: str
    source: Source


@final
@dataclass(frozen=True)
class Target:
    name: str  # TODO Maybe remove name and store in project as Dict

    main_file: Path  # relative to source folder
    backend: KompileBackend
    main_module: str | None
    syntax_module: str | None
    md_selector: str | None
    hook_namespaces: tuple[str, ...] | None
    emit_json: bool | None
    gen_bison_parser: bool | None
    # LLVM backend
    opt_level: int | None
    ccopts: tuple[str, ...] | None
    no_llvm_kompile: bool | None
    enable_search: bool | None
    # Haskell backend
    concrete_rules: tuple[str, ...] | None

    def __init__(
        self,
        *,
        name: str,
        main_file: str | Path,
        backend: KompileBackend,
        main_module: str | None = None,
        syntax_module: str | None = None,
        md_selector: str | None = None,
        hook_namespaces: Iterable[str] | None = None,
        emit_json: bool | None = None,
        gen_bison_parser: bool | None = None,
        opt_level: int | None = None,
        ccopts: Iterable[str] | None = None,
        no_llvm_kompile: bool | None = None,
        enable_search: bool | None = None,
        concrete_rules: Iterable[str] | None = None,
    ):
        main_file = Path(main_file)
        check_relative_path(main_file)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'main_file', main_file)
        object.__setattr__(self, 'backend', backend)
        object.__setattr__(self, 'main_module', main_module)
        object.__setattr__(self, 'syntax_module', syntax_module)
        object.__setattr__(self, 'md_selector', md_selector)
        object.__setattr__(self, 'hook_namespaces', tuple(hook_namespaces) if hook_namespaces is not None else None)
        object.__setattr__(self, 'emit_json', emit_json)
        object.__setattr__(self, 'gen_bison_parser', gen_bison_parser)
        object.__setattr__(self, 'opt_level', opt_level)
        object.__setattr__(self, 'ccopts', tuple(ccopts) if ccopts is not None else None)
        object.__setattr__(self, 'no_llvm_kompile', no_llvm_kompile)
        object.__setattr__(self, 'enable_search', enable_search)
        object.__setattr__(self, 'concrete_rules', tuple(concrete_rules) if concrete_rules is not None else None)

    @staticmethod
    def from_dict(name: str, dct: Mapping[str, Any]) -> Target:
        return Target(
            name=name,
            main_file=Path(dct['main-file']),
            backend=KompileBackend(dct['backend']),
            main_module=dct.get('main-module'),
            syntax_module=dct.get('syntax-module'),
            md_selector=dct.get('md-selector'),
            hook_namespaces=dct.get('hook-namespaces'),
            emit_json=dct.get('emit-json'),
            gen_bison_parser=dct.get('gen-bison-parser'),
            opt_level=dct.get('opt-level'),
            ccopts=dct.get('ccopts'),
            no_llvm_kompile=dct.get('no-llvm-kompile'),
            enable_search=dct.get('enable-search'),
            concrete_rules=dct.get('concrete-rules'),
        )

    @property
    def dict(self) -> dict[str, Any]:
        dct = dataclasses.asdict(self)
        return {key: value for key, value in dct.items() if value is not None}


@final
@dataclass(frozen=True)
class Project:
    path: Path
    name: str
    version: str
    source_dir: Path
    resources: FrozenDict[str, Path]
    dependencies: tuple[Dependency, ...]
    targets: tuple[Target, ...]

    def __init__(
        self,
        *,
        path: str | Path,
        name: str,
        version: str,
        source_dir: str | Path,
        resources: Mapping[str, str | Path] | None = None,
        dependencies: Iterable[Dependency] = (),
        targets: Iterable[Target] = (),
    ):
        path = Path(path).resolve()
        check_dir_path(path)

        source_dir = (path / relative_path(source_dir)).resolve()
        check_dir_path(source_dir)

        resources = resources or {}
        resources = {
            resource_name: (path / relative_path(resource_dir)).resolve()
            for resource_name, resource_dir in resources.items()
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

        with open(project_file, 'rb') as f:
            dct = tomli.load(f)

        project_dir = project_file.parent.resolve()

        return Project(
            path=project_dir,
            name=dct['project']['name'],
            version=dct['project']['version'],
            source_dir=dct['project']['source'],
            resources=dct['project'].get('resources'),
            dependencies=tuple(
                Dependency(name=name, source=Source.from_dict(project_dir, source))
                for name, source in dct.get('dependencies', {}).items()
            ),
            targets=tuple(Target.from_dict(name, target) for name, target in dct.get('targets', {}).items()),
        )

    @staticmethod
    def load_from_dir(project_dir: str | Path) -> Project:
        project_dir = Path(project_dir)
        check_dir_path(project_dir)
        return Project.load(project_dir / PROJECT_FILE_NAME)

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

    def get_target(self, target_name: str) -> Target:
        # TODO Should be enforced as a validation rule
        return single(target for target in self.targets if target.name == target_name)
