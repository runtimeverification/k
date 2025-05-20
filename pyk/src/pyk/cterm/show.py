from __future__ import annotations

import logging
from dataclasses import dataclass
from typing import TYPE_CHECKING

from ..kast.inner import KApply, KSort, KToken, flatten_label, top_down
from ..kast.manip import free_vars, minimize_term
from ..kast.prelude.k import DOTS
from .cterm import CTerm

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable
    from typing import Final

    from ..kast.inner import KInner

_LOGGER: Final = logging.getLogger(__name__)


@dataclass
class CTermShow:
    _printer: Callable[[KInner], str]
    _minimize: bool
    _break_cell_collections: bool
    _omit_labels: tuple[str, ...]

    def __init__(
        self,
        printer: Callable[[KInner], str],
        minimize: bool = True,
        break_cell_collections: bool = True,
        omit_labels: Iterable[str] = (),
    ):
        self._printer = printer
        self._minimize = minimize
        self._break_cell_collections = break_cell_collections
        self._omit_labels = tuple(omit_labels)

    def print_lines(self, kast: KInner) -> list[str]:
        return self._printer(kast).split('\n')

    def let(
        self,
        minimize: bool | None = None,
        break_cell_collections: bool | None = None,
        omit_labels: Iterable[str] | None = None,
    ) -> CTermShow:
        return CTermShow(
            self._printer,
            minimize=(self._minimize if minimize is None else minimize),
            break_cell_collections=(
                self._break_cell_collections if break_cell_collections is None else break_cell_collections
            ),
            omit_labels=(self._omit_labels if omit_labels is None else omit_labels),
        )

    def show(self, cterm: CTerm) -> list[str]:
        ret_strs: list[str] = []
        ret_strs.extend(self.show_config(cterm))
        ret_strs.extend(self.show_constraints(cterm))
        return ret_strs

    def show_config(self, cterm: CTerm) -> list[str]:
        if self._break_cell_collections:
            cterm = CTerm(top_down(self._break_cells_visitor, cterm.config), cterm.constraints)
        if self._omit_labels:
            cterm = CTerm(top_down(self._omit_labels_visitor, cterm.config), cterm.constraints)
        if self._minimize:
            cterm = CTerm(minimize_term(cterm.config, keep_vars=free_vars(cterm.constraint)), cterm.constraints)
        return self.print_lines(cterm.config)

    def show_constraints(self, cterm: CTerm) -> list[str]:
        ret_strs: list[str] = []
        for constraint in cterm.constraints:
            constraint_strs = self.print_lines(constraint)
            if len(constraint_strs) > 0:
                constraint_strs = [f'#And {cstr}' for cstr in constraint_strs]
                ret_strs.append(constraint_strs[0])
                ret_strs.extend([f'  {constraint_str}' for constraint_str in constraint_strs[1:]])
        return ret_strs

    def _break_cells_visitor(self, kast: KInner) -> KInner:
        if (
            type(kast) is KApply
            and kast.is_cell
            and len(kast.args) == 1
            and type(kast.args[0]) is KApply
            and kast.args[0].label.name in {'_Set_', '_List_', '_Map_'}
        ):
            items = flatten_label(kast.args[0].label.name, kast.args[0])
            printed = KToken('\n'.join(map(self._printer, items)), KSort(kast.label.name[1:-1]))
            return KApply(kast.label, [printed])
        return kast

    def _omit_labels_visitor(self, kast: KInner) -> KInner:
        if type(kast) == KApply and kast.label.name in self._omit_labels:
            return DOTS
        return kast
