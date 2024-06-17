from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from functools import cached_property, partial
from graphlib import TopologicalSorter
from typing import TYPE_CHECKING

from ..kast import Atts
from ..kast.outer import KClaim
from ..utils import FrozenDict, unique

if TYPE_CHECKING:
    from collections.abc import Container, Iterable, Iterator

    from ..kast.outer import KFlatModule, KFlatModuleList


@dataclass(frozen=True)
class ClaimIndex(Mapping[str, KClaim]):
    claims: FrozenDict[str, KClaim]
    main_module_name: str | None

    def __init__(
        self,
        claims: Mapping[str, KClaim],
        main_module_name: str | None = None,
    ):
        self._validate(claims)
        object.__setattr__(self, 'claims', FrozenDict(claims))
        object.__setattr__(self, 'main_module_name', main_module_name)

    @staticmethod
    def from_module_list(module_list: KFlatModuleList) -> ClaimIndex:
        module_list = ClaimIndex._resolve_depends(module_list)
        return ClaimIndex(
            claims={claim.label: claim for module in module_list.modules for claim in module.claims},
            main_module_name=module_list.main_module,
        )

    @staticmethod
    def _validate(claims: Mapping[str, KClaim]) -> None:
        for label, claim in claims.items():
            if claim.label != label:
                raise ValueError(f'Claim label mismatch, expected: {label}, found: {claim.label}')

            for depend in claim.dependencies:
                if depend not in claims:
                    raise ValueError(f'Invalid dependency label: {depend}')

    @staticmethod
    def _resolve_depends(module_list: KFlatModuleList) -> KFlatModuleList:
        """Resolve each depends value relative to the module the claim belongs to.

        Example:
            ```
            module THIS-MODULE
                claim ... [depends(foo,OTHER-MODULE.bar)]
            endmodule
            ```

            becomes

            ```
            module THIS-MODULE
                claim ... [depends(THIS-MODULE.foo,OTHER-MODULE.bar)]
            endmodule
            ```
        """
        labels = {claim.label for module in module_list.modules for claim in module.claims}

        def resolve_claim_depends(module_name: str, claim: KClaim) -> KClaim:
            depends = claim.dependencies
            if not depends:
                return claim

            resolve = partial(ClaimIndex._resolve_claim_label, labels, module_name)
            resolved = [resolve(label) for label in depends]
            return claim.let(att=claim.att.update([Atts.DEPENDS(','.join(resolved))]))

        modules: list[KFlatModule] = []
        for module in module_list.modules:
            resolve_depends = partial(resolve_claim_depends, module.name)
            module = module.map_sentences(resolve_depends, of_type=KClaim)
            modules.append(module)

        return module_list.let(modules=modules)

    @staticmethod
    def _resolve_claim_label(labels: Container[str], module_name: str | None, label: str) -> str:
        """Resolve `label` to a valid label in `labels`, or raise.

        If a `label` is not found and `module_name` is set, the label is tried after qualifying.
        """
        if label in labels:
            return label

        if module_name is not None:
            qualified = f'{module_name}.{label}'
            if qualified in labels:
                return qualified

        raise ValueError(f'Claim label not found: {label}')

    def __iter__(self) -> Iterator[str]:
        return iter(self.claims)

    def __len__(self) -> int:
        return len(self.claims)

    def __getitem__(self, label: str) -> KClaim:
        try:
            label = self.resolve(label)
        except ValueError:
            raise KeyError(f'Claim not found: {label}') from None
        return self.claims[label]

    @cached_property
    def topological(self) -> tuple[str, ...]:
        graph = {label: claim.dependencies for label, claim in self.claims.items()}
        return tuple(TopologicalSorter(graph).static_order())

    def resolve(self, label: str) -> str:
        return self._resolve_claim_label(self.claims, self.main_module_name, label)

    def resolve_all(self, labels: Iterable[str]) -> list[str]:
        return [self.resolve(label) for label in unique(labels)]

    def labels(
        self,
        *,
        include: Iterable[str] | None = None,
        exclude: Iterable[str] | None = None,
        with_depends: bool = True,
    ) -> list[str]:
        res: list[str] = []

        pending = self.resolve_all(include) if include is not None else list(self.claims)
        done = set(self.resolve_all(exclude)) if exclude is not None else set()

        while pending:
            label = pending.pop(0)  # BFS

            if label in done:
                continue

            res.append(label)
            done.add(label)

            if with_depends:
                pending += self.claims[label].dependencies

        return res
