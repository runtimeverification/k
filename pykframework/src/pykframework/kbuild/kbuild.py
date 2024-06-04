from __future__ import annotations

import re
from contextlib import contextmanager
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING, final

from filelock import FileLock

from ..ktool.kompile import kompile
from ..utils import check_dir_path, single
from .utils import k_version, sync_files

if TYPE_CHECKING:
    from collections.abc import Iterator
    from re import Match
    from typing import Any

    from .project import Project, Target


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

    def definition_dir(self, project: Project, target_name: str) -> Path:
        return self.kdist_dir / self.k_version / target_name

    def kompile(self, project: Project, target_name: str, *, debug: bool = False) -> Path:
        self.kdist_dir.mkdir(parents=True, exist_ok=True)

        with FileLock(self.kdist_dir / '.lock'):
            output_dir = self.definition_dir(project, target_name)

            if self.up_to_date(project, target_name):
                return output_dir

            with KBuildEnv.create_temp(project) as env:
                env.kompile(target_name, output_dir, debug=debug)

            return output_dir

    def up_to_date(self, project: Project, target_name: str) -> bool:
        definition_dir = self.definition_dir(project, target_name)
        timestamp = definition_dir / 'timestamp'

        if not timestamp.exists():
            return False

        input_timestamps = (input_file.stat().st_mtime for input_file in project.all_files)
        target_timestamp = timestamp.stat().st_mtime
        return all(input_timestamp < target_timestamp for input_timestamp in input_timestamps)


@final
@dataclass(frozen=True)
class KBuildEnv:
    project: Project
    path: Path

    def __init__(self, project: Project, path: str | Path):
        path = Path(path).resolve()
        check_dir_path(path)
        object.__setattr__(self, 'project', project)
        object.__setattr__(self, 'path', path)

    @staticmethod
    @contextmanager
    def create_temp(project: Project) -> Iterator[KBuildEnv]:
        with TemporaryDirectory(prefix=f'kbuild-{project.name}-') as path_str:
            env = KBuildEnv(project, path_str)
            env.sync()
            yield env

    def sync(self) -> None:
        for sub_project in self.project.sub_projects:
            self._sync_project(sub_project)

    def kompile(self, target_name: str, output_dir: Path, *, debug: bool = False) -> None:
        target = self.project.get_target(target_name)
        kompile(
            output_dir=output_dir,
            include_dirs=self._include_dirs,
            cwd=self.path,
            debug=debug,
            **self._kompile_args(target),
        )

    @property
    def _include_dirs(self) -> list[Path]:
        return [self._include_dir(sub_project) for sub_project in self.project.sub_projects]

    def _include_dir(self, project: Project) -> Path:
        return self.path / project.name / 'include'

    def _source_dir(self, project: Project) -> Path:
        return self._include_dir(project) / project.name

    def _resource_dir(self, project: Project, resource_name: str) -> Path:
        return self.path / project.name / 'resource' / resource_name

    def _sync_project(self, project: Project) -> None:
        # Sync sources
        sync_files(
            source_dir=project.source_dir,
            target_dir=self._source_dir(project),
            file_names=project.source_file_names,
        )

        # Sync resources
        for resource_name in project.resources:
            sync_files(
                source_dir=project.resources[resource_name],
                target_dir=self._resource_dir(project, resource_name),
                file_names=project.resource_file_names[resource_name],
            )

    def _kompile_args(self, target: Target) -> dict[str, Any]:
        args = dict(target.args)
        args['main_file'] = self._source_dir(self.project) / args['main_file']

        if 'ccopts' in args:
            args['ccopts'] = [self._render_opt(opt) for opt in args['ccopts']]

        return args

    def _render_opt(self, opt: str) -> str:
        def render(match: Match) -> str:
            project_name = match.group('project')
            resource_name = match.group('resource')

            sub_project = single(
                sub_project for sub_project in self.project.sub_projects if sub_project.name == project_name
            )
            resource_path = self._resource_dir(sub_project, resource_name)

            if not resource_path.exists():
                raise ValueError('Failed to resolve opt {opt}: resource path {resource_path} does not exist')

            return str(resource_path)

        pattern = re.compile(r'{{ *(?P<project>\S+):(?P<resource>\S+) *}}')
        return pattern.sub(render, opt)
