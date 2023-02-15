from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from typing import List, Tuple, Union, final

from ..utils import hash_str
from .project import Dependency, GitSource, PathSource, Project, Source


class Package(ABC):
    @staticmethod
    def create(project_file: Union[str, Path]) -> 'Package':
        project = Project.load(project_file)
        return _RootPackage(project)

    @property
    @abstractmethod
    def name(self) -> str:
        ...

    @property
    @abstractmethod
    def source(self) -> Source:
        ...

    @property
    @abstractmethod
    def project(self) -> Project:
        ...

    @property
    def path(self) -> Path:
        return Path(self.name) / hash_str(self.source)[:7]

    @property
    def target_dir(self) -> Path:
        return self.path / 'target'

    @property
    def include_dir(self) -> Path:
        return self.path / 'include'

    @property
    def include_dirs(self) -> List[Path]:
        return [package.include_dir for package in self.sub_packages]

    @property
    def include_files(self) -> List[Path]:
        return [self.include_dir / self.name / file_name for file_name in self.project.include_file_names]

    @cached_property
    def deps_packages(self) -> Tuple['Package', ...]:
        return tuple(_DepsPackage(dependency) for dependency in self.project.dependencies)

    @cached_property
    def sub_packages(self) -> Tuple['Package', ...]:
        res: Tuple[Package, ...] = (self,)
        for package in self.deps_packages:
            res += package.sub_packages
        return res


@final
@dataclass(frozen=True)
class _RootPackage(Package):
    _project: Project

    @property
    def name(self) -> str:
        return self.project.name

    @property
    def source(self) -> Source:
        return PathSource(self.project.path)

    @property
    def project(self) -> Project:
        return self._project


@final
@dataclass(frozen=True)
class _DepsPackage(Package):
    dependency: Dependency

    @property
    def name(self) -> str:
        return self.dependency.name

    @property
    def source(self) -> Source:
        return self.dependency.source

    @property
    def project(self) -> Project:
        project_path = self.sync_project()
        project = Project.load_from_dir(project_path)
        if self.name != project.name:
            raise ValueError(f'Expected {self.name} as project name, found: {project.name}')
        return project

    def sync_project(self) -> Path:
        if type(self.source) is PathSource:
            return self.source.path

        # TODO Clone if necessary then checkout
        assert type(self.source) is GitSource
        raise RuntimeError('Git sources are not supported yet')
