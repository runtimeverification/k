from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from ..kast.inner import KApply
from ..kast.manip import free_vars, minimize_term
from ..kast.prelude.kbool import TRUE
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
    boolify: bool
    minimize: bool

    def __init__(
        self,
        definition: KDefinition,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
        patch_symbol_table: Callable[[SymbolTable], None] | None = None,
        unalias: bool = True,
        sort_collections: bool = False,
        adjust_cterm: Callable[[CTerm], CTerm] | None = None,
        boolify: bool = False,
        minimize: bool = False,
    ):
        super().__init__(
            definition,
            extra_unparsing_modules,
            patch_symbol_table,
            unalias,
            sort_collections,
        )
        self.adjust_cterm = adjust_cterm
        self.boolify = boolify
        self.minimize = minimize

    def let(
        self,
        unalias: bool | None = None,
        sort_collections: bool | None = None,
        adjust_cterm: Callable[[CTerm], CTerm] | None = None,
        boolify: bool | None = None,
        minimize: bool | None = None,
    ) -> CTermShow:
        return CTermShow(
            self.definition,
            extra_unparsing_modules=self._extra_unparsing_modules,
            patch_symbol_table=self._patch_symbol_table,
            unalias=(self._unalias if unalias is None else unalias),
            sort_collections=(self._sort_collections if sort_collections is None else sort_collections),
            adjust_cterm=(self.adjust_cterm if adjust_cterm is None else adjust_cterm),
            boolify=(self.boolify if boolify is None else boolify),
            minimize=(self.minimize if minimize is None else minimize),
        )

    def show(self, cterm: CTerm, omit_config: bool = False, omit_constraints: bool = False) -> list[str]:
        def _boolify(c: KInner) -> KInner:
            if type(c) is KApply and c.label.name == '#Equals' and c.args[0] == TRUE:
                return c.args[1]
            else:
                return c

        if self.adjust_cterm:
            cterm = self.adjust_cterm(cterm)

        if self.minimize:
            cterm = CTerm(minimize_term(cterm.config, keep_vars=free_vars(cterm.constraint)), cterm.constraints)

        if omit_constraints:
            cterm = CTerm(cterm.config)
        elif self.boolify:
            cterm = CTerm(cterm.config, map(_boolify, cterm.constraints))

        ret_strs: list[str] = []
        if not omit_config:
            ret_strs.extend(self.print(cterm.config).split('\n'))
        if not omit_constraints:
            for constraint in cterm.constraints:
                constraint_strs = self.print(constraint).split('\n')
                if len(constraint_strs) > 0:
                    if not self.boolify:
                        constraint_strs = [f'#And {cstr}' for cstr in constraint_strs]
                    ret_strs.append(constraint_strs[0])
                    ret_strs.extend([f'  {constraint_str}' for constraint_str in constraint_strs[1:]])
        return ret_strs
