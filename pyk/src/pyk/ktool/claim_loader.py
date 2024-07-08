from __future__ import annotations

import json
from typing import TYPE_CHECKING, NamedTuple

from ..kast.outer import KFlatModuleList
from ..kast.utils import slurp_definitions
from ..utils import hash_str
from .claim_index import ClaimIndex

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from pathlib import Path
    from typing import Any

    from ..kast.outer import KClaim
    from . import TypeInferenceMode
    from .kprove import KProve


class ClaimLoader:
    _kprove: KProve

    def __init__(self, kprove: KProve):
        self._kprove = kprove

    def load_claims(
        self,
        spec_file: Path,
        *,
        spec_module_name: str | None = None,
        include_dirs: Iterable[Path] = (),
        md_selector: str | None = None,
        claim_labels: Iterable[str] | None = None,
        exclude_claim_labels: Iterable[str] | None = None,
        include_dependencies: bool = True,
        type_inference_mode: TypeInferenceMode | None = None,
    ) -> list[KClaim]:
        digest = self._digest(spec_file, include_dirs=include_dirs, md_selector=md_selector)

        claim_file = spec_file.with_suffix('.json')

        cache_hit = False
        if claim_file.exists():
            module_list, _digest = _ClaimModuleList.from_dict(json.loads(claim_file.read_text()))
            cache_hit = digest == _digest

        if not cache_hit:
            module_list = self._kprove.get_claim_modules(
                spec_file=spec_file,
                spec_module_name=spec_module_name,
                include_dirs=include_dirs,
                md_selector=md_selector,
                type_inference_mode=type_inference_mode,
            )
            claim_module_list = _ClaimModuleList(module_list=module_list, digest=digest)
            claim_file.write_text(json.dumps(claim_module_list.to_dict()))

        claim_index = ClaimIndex.from_module_list(module_list)

        labels = claim_index.labels(
            include=claim_labels,
            exclude=exclude_claim_labels,
            with_depends=include_dependencies,
        )

        return [claim_index[label] for label in labels]

    @staticmethod
    def _digest(spec_file: Path, *, include_dirs: Iterable[Path], md_selector: str | None) -> str:
        from .utils import K_DISTRIBUTION

        definitions = slurp_definitions(
            spec_file,
            include_dirs=list(include_dirs) + ([K_DISTRIBUTION.builtin_dir] if K_DISTRIBUTION else []),
            md_selector=md_selector,
        )
        definitions = {key: definitions[key] for key in sorted(definitions)}
        return hash_str(definitions)


class _ClaimModuleList(NamedTuple):
    module_list: KFlatModuleList
    digest: str

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> _ClaimModuleList:
        return _ClaimModuleList(
            module_list=KFlatModuleList.from_dict(dct['moduleList']),
            digest=dct['digest'],
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            'moduleList': self.module_list.to_dict(),
            'digest': self.digest,
        }
