import dataclasses
from abc import ABC
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Tuple, Union, final

import tomli

from ..cli_utils import abs_or_rel_to, check_absolute_path, check_dir_path, check_file_path, check_relative_path
from ..ktool.kompile import KompileBackend
from ..utils import single
from .config import PROJECT_FILE_NAME


class Source(ABC):  # noqa: B024
    @staticmethod
    def from_dict(project_dir: Path, dct: Mapping[str, Any]) -> 'Source':
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
    def from_dict(project_dir: Path, dct: Mapping[str, Any]) -> 'PathSource':
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
    main_module: Optional[str]
    syntax_module: Optional[str]
    md_selector: Optional[str]
    hook_namespaces: Optional[Tuple[str, ...]]
    emit_json: Optional[bool]

    def __init__(
        self,
        *,
        name: str,
        main_file: Union[str, Path],
        backend: KompileBackend,
        main_module: Optional[str] = None,
        syntax_module: Optional[str] = None,
        md_selector: Optional[str] = None,
        hook_namespaces: Optional[Iterable[str]] = None,
        emit_json: Optional[bool] = None,
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

    @staticmethod
    def from_dict(name: str, dct: Mapping[str, Any]) -> 'Target':
        return Target(
            name=name,
            main_file=Path(dct['main-file']),
            backend=KompileBackend(dct['backend']),
            main_module=dct.get('main-module'),
            syntax_module=dct.get('syntax-module'),
            md_selector=dct.get('md-selector'),
            hook_namespaces=dct.get('hook-namespaces'),
            emit_json=dct.get('emit-json'),
        )

    def kompile_args(self) -> Dict[str, Any]:
        args = dataclasses.asdict(self)
        args.pop('name')
        return args


@final
@dataclass(frozen=True)
class Project:
    path: Path
    name: str
    version: str
    source_dir: Path
    dependencies: Tuple[Dependency, ...]
    targets: Tuple[Target, ...]

    def __init__(
        self,
        *,
        path: Union[str, Path],
        name: str,
        version: str,
        source_dir: Union[str, Path],
        dependencies: Iterable[Dependency] = (),
        targets: Iterable[Target] = (),
    ):
        path = Path(path).resolve()
        check_dir_path(path)
        check_absolute_path(path)

        source_dir = Path(source_dir)
        # TODO extract
        if source_dir.is_absolute():
            source_dir = source_dir.resolve()
            # TODO Lift this restriction: check source_dir.is_relative_to(path)
            raise ValueError(f'Expected relative path for source_dir, got: {source_dir}')
        else:
            source_dir = (path / source_dir).resolve()

        check_dir_path(source_dir)

        object.__setattr__(self, 'path', path)
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'version', version)
        object.__setattr__(self, 'source_dir', source_dir)
        object.__setattr__(self, 'dependencies', tuple(dependencies))
        object.__setattr__(self, 'targets', tuple(targets))

    @staticmethod
    def load(project_file: Union[str, Path]) -> 'Project':
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
            dependencies=tuple(
                Dependency(name=name, source=Source.from_dict(project_dir, source))
                for name, source in dct.get('dependencies', {}).items()
            ),
            targets=tuple(Target.from_dict(name, target) for name, target in dct.get('targets', {}).items()),
        )

    @staticmethod
    def load_from_dir(project_dir: Union[str, Path]) -> 'Project':
        project_dir = Path(project_dir)
        check_dir_path(project_dir)
        return Project.load(project_dir / PROJECT_FILE_NAME)

    @property
    def include_file_names(self) -> List[str]:
        source_files = list(self.source_dir.rglob('*.k'))
        source_files.extend(self.source_dir.rglob('*.md'))
        return [str(source_file.relative_to(self.source_dir)) for source_file in source_files]

    @property
    def include_files(self) -> List[Path]:
        return [self.source_dir / file_name for file_name in self.include_file_names]

    @property
    def project_file(self) -> Path:
        return self.path / PROJECT_FILE_NAME

    def get_target(self, target_name: str) -> Target:
        # TODO Should be enforced as a validation rule
        return single(target for target in self.targets if target.name == target_name)
