from __future__ import annotations

from typing import TYPE_CHECKING, NamedTuple

from ..kast.outer import KFlatModuleList

if TYPE_CHECKING:
    from collections.abc import Mapping
    from typing import Any


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
