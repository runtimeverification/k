from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from ..kast.inner import KApply, KSort, KToken, flatten_label, top_down
from ..kast.manip import free_vars, minimize_term
from ..kast.pretty import PrettyPrinter
from .cterm import CTerm

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable
    from typing import Final

    from ..kast.inner import KInner
    from ..kast.outer import KDefinition, KFlatModule
    from ..kast.pretty import SymbolTable

_LOGGER: Final = logging.getLogger(__name__)


class CTermShow(PrettyPrinter):
    adjust_cterm: Callable[[CTerm], CTerm] | None
    minimize: bool
    break_cell_collections: bool

    def __init__(
        self,
        definition: KDefinition,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
        patch_symbol_table: Callable[[SymbolTable], None] | None = None,
        unalias: bool = True,
        sort_collections: bool = True,
        adjust_cterm: Callable[[CTerm], CTerm] | None = None,
        minimize: bool = True,
        break_cell_collections: bool = True,
    ):
        super().__init__(
            definition,
            extra_unparsing_modules,
            patch_symbol_table,
            unalias,
            sort_collections,
        )
        self.adjust_cterm = adjust_cterm
        self.minimize = minimize
        self.break_cell_collections = break_cell_collections

    def let(
        self,
        unalias: bool | None = None,
        sort_collections: bool | None = None,
        adjust_cterm: Callable[[CTerm], CTerm] | None = None,
        minimize: bool | None = None,
        break_cell_collections: bool | None = None,
    ) -> CTermShow:
        return CTermShow(
            self.definition,
            extra_unparsing_modules=self._extra_unparsing_modules,
            patch_symbol_table=self._patch_symbol_table,
            unalias=(self._unalias if unalias is None else unalias),
            sort_collections=(self._sort_collections if sort_collections is None else sort_collections),
            adjust_cterm=(self.adjust_cterm if adjust_cterm is None else adjust_cterm),
            minimize=(self.minimize if minimize is None else minimize),
            break_cell_collections=(
                self.break_cell_collections if break_cell_collections is None else break_cell_collections
            ),
        )

    def _break_cell_collections(self, kast: KInner) -> KInner:
        if (
            type(kast) is KApply
            and kast.is_cell
            and len(kast.args) == 1
            and type(kast.args[0]) is KApply
            and kast.args[0].label.name in {'_Set_', '_List_', '_Map_'}
        ):
            items = flatten_label(kast.args[0].label.name, kast.args[0])
            printed = KToken('\n'.join(map(self.print, items)), KSort(kast.label.name[1:-1]))
            return KApply(kast.label, [printed])
        return kast

    def show(self, cterm: CTerm, omit_config: bool = False, omit_constraints: bool = False) -> list[str]:
        if self.adjust_cterm:
            cterm = self.adjust_cterm(cterm)

        if self.minimize:
            cterm = CTerm(minimize_term(cterm.config, keep_vars=free_vars(cterm.constraint)), cterm.constraints)

        if omit_constraints:
            cterm = CTerm(cterm.config)

        ret_strs: list[str] = []

        if not omit_config:
            if self.break_cell_collections:
                cterm = CTerm(top_down(self._break_cell_collections, cterm.config), cterm.constraints)
            ret_strs.extend(self.print(cterm.config).split('\n'))

        if not omit_constraints:
            for constraint in cterm.constraints:
                constraint_strs = self.print(constraint).split('\n')
                if len(constraint_strs) > 0:
                    constraint_strs = [f'#And {cstr}' for cstr in constraint_strs]
                    ret_strs.append(constraint_strs[0])
                    ret_strs.extend([f'  {constraint_str}' for constraint_str in constraint_strs[1:]])

        return ret_strs
