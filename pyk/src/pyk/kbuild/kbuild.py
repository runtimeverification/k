from __future__ import annotations

import re
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
        return self.kdist_dir / project.name / 'target' / self.k_version / target_name

    def resource_dir(self, project: Project, resource_name: str) -> Path:
        return self.kdist_dir / project.name / 'resource' / resource_name

    def resource_files(self, project: Project, resource_name: str) -> list[Path]:
        return [
            self.resource_dir(project, resource_name) / file_name
            for file_name in project.resource_file_names[resource_name]
        ]

    def include_dir(self, project: Project) -> Path:
        return self.kdist_dir / project.name / 'include'

    def source_dir(self, project: Project) -> Path:
        return self.include_dir(project) / project.name

    def source_files(self, project: Project) -> list[Path]:
        return [self.source_dir(project) / file_name for file_name in project.source_file_names]

    def sync(self, project: Project) -> list[Path]:
        res: list[Path] = []

        # Sync sources
        res += sync_files(
            source_dir=project.source_dir,
            target_dir=self.source_dir(project),
            file_names=project.source_file_names,
        )

        # Sync resources
        for resource_name in project.resources:
            res += sync_files(
                source_dir=project.resources[resource_name],
                target_dir=self.resource_dir(project, resource_name),
                file_names=project.resource_file_names[resource_name],
            )

        return res

    def kompile(self, project: Project, target_name: str) -> Path:
        self.kdist_dir.mkdir(parents=True, exist_ok=True)
        with FileLock(self.kdist_dir / '.lock'):
            for sub_project in project.sub_projects:
                self.sync(sub_project)

            output_dir = self.definition_dir(project, target_name)

            if self.up_to_date(project, target_name):
                return output_dir

            target = project.get_target(target_name)
            args = self.kompile_args(project, target)
            kompile(
                output_dir=output_dir,
                include_dirs=[self.include_dir(sub_project) for sub_project in project.sub_projects],
                cwd=self.kdist_dir,
                **args,
            )

            return output_dir

    def up_to_date(self, project: Project, target_name: str) -> bool:
        definition_dir = self.definition_dir(project, target_name)
        timestamp = definition_dir / 'timestamp'

        if not timestamp.exists():
            return False

        input_files: list[Path] = []
        for sub_project in project.sub_projects:
            input_files.append(sub_project.project_file)
            input_files.extend(self.source_files(sub_project))
            for resource_name in sub_project.resources:
                input_files.extend(self.resource_files(sub_project, resource_name))

        input_timestamps = (input_file.stat().st_mtime for input_file in input_files)
        target_timestamp = timestamp.stat().st_mtime
        return all(input_timestamp < target_timestamp for input_timestamp in input_timestamps)

    def kompile_args(self, project: Project, target: Target) -> dict[str, Any]:
        args = target.dict
        args.pop('name')
        args['main_file'] = self.source_dir(project) / args['main_file']

        if 'ccopts' in args:
            args['ccopts'] = [self.render_opt(project, opt) for opt in args['ccopts']]

        return args

    def render_opt(self, project: Project, opt: str) -> str:
        def render(match: Match) -> str:
            project_name = match.group('project')
            resource_name = match.group('resource')

            sub_project = single(
                sub_project for sub_project in project.sub_projects if sub_project.name == project_name
            )
            resource_path = self.resource_dir(sub_project, resource_name)

            if not resource_path.exists():
                raise ValueError('Failed to resolve opt {opt}: resource path {resource_path} does not exist')

            return str(resource_path)

        pattern = re.compile(r'{{ *(?P<project>\S+):(?P<resource>\S+) *}}')
        return pattern.sub(render, opt)
