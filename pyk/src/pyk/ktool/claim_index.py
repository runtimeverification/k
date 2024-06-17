from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from functools import partial
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
        ordered: bool = False,
    ) -> list[str]:
        """Return a list of labels from the index.

        Args:
            include: Labels to include in the result. If `None`, all labels are included.
            exclude: Labels to exclude from the result. If `None`, no labels are excluded.
              Takes precedence over `include`.
            with_depends: If `True`, the result is transitively closed w.r.t. the dependency relation.
              Labels in `exclude` are pruned, and their dependencies are not considered on the given path.
            ordered: If `True`, the result is topologically sorted w.r.t. the dependency relation.

        Returns:
            A list of labels from the index.

        Raises:
            ValueError: If an item in `include` or `exclude` cannot be resolved to a valid label.
        """
        include = self.resolve_all(include) if include is not None else self.claims
        exclude = self.resolve_all(exclude) if exclude is not None else []

        labels: list[str]

        if with_depends:
            labels = self._close_dependencies(labels=include, prune=exclude)
        else:
            labels = [label for label in include if label not in set(exclude)]

        if ordered:
            return self._sort_topologically(labels)

        return labels

    def _close_dependencies(self, labels: Iterable[str], prune: Iterable[str]) -> list[str]:
        res: list[str] = []

        pending = list(labels)
        done = set(prune)

        while pending:
            label = pending.pop(0)  # BFS

            if label in done:
                continue

            res.append(label)
            pending += self.claims[label].dependencies
            done.add(label)

        return res

    def _sort_topologically(self, labels: list[str]) -> list[str]:
        label_set = set(labels)
        graph = {
            label: [dep for dep in claim.dependencies if dep in label_set]
            for label, claim in self.claims.items()
            if label in labels
        }
        return list(TopologicalSorter(graph).static_order())
