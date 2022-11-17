from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from typing import List, Tuple, final

from ..ktool import kompile
from ..utils import hash_str
from .config import KBUILD_DIR
from .project import Dependency, GitSource, PathSource, Project, Source
from .utils import k_version, sync_files


class Package(ABC):
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
        return KBUILD_DIR / self.name / hash_str(self.source)[:7]

    @property
    def target_dir(self) -> Path:
        return self.path / 'target'

    @property
    def include_dir(self) -> Path:
        return self.path / 'include'

    @property
    def include_dirs(self) -> List[Path]:
        return [package.include_dir for package in (self,) + self.deps_packages]

    @property
    def include_files(self) -> List[Path]:
        return [self.include_dir / self.name / file_name for file_name in self.project.include_file_names]

    @cached_property
    def k_version(self) -> str:
        return k_version().text

    @cached_property
    def deps_packages(self) -> Tuple['Package', ...]:
        return tuple(DepsPackage(dependency) for dependency in self.project.dependencies)

    @cached_property
    def packages(self) -> Tuple['Package', ...]:
        res: Tuple[Package, ...] = (self,)
        for package in self.deps_packages:
            res += package.packages
        return res

    def kompile(self, target_name: str) -> Path:
        for package in self.packages:
            package.sync()

        output_dir = self.definition_dir(target_name)

        if self.up_to_date(target_name):
            return output_dir

        target = self.project.get_target(target_name)
        kompile(
            output_dir=output_dir,
            include_dirs=self.include_dirs,
            cwd=self.include_dir / self.name,
            **target.kompile_args(),
        )

        return output_dir

    def sync(self) -> List[Path]:
        return sync_files(
            source_dir=self.project.source_dir,
            target_dir=self.include_dir / self.name,
            file_names=self.project.include_file_names,
        )

    def definition_dir(self, target_name: str) -> Path:
        return self.target_dir / self.k_version / target_name

    def up_to_date(self, target_name: str) -> bool:
        definition_dir = self.definition_dir(target_name)
        timestamp = definition_dir / 'timestamp'

        if not timestamp.exists():
            return False

        input_files: List[Path] = []
        for package in self.packages:
            input_files.append(package.project.project_file)
            input_files.extend(package.include_files)

        input_timestamps = (input_file.stat().st_mtime for input_file in input_files)
        target_timestamp = timestamp.stat().st_mtime
        return all(input_timestamp < target_timestamp for input_timestamp in input_timestamps)


@final
@dataclass(frozen=True)
class RootPackage(Package):
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
class DepsPackage(Package):
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
