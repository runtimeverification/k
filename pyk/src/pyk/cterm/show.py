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

    def __init__(
        self,
        definition: KDefinition,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
        patch_symbol_table: Callable[[SymbolTable], None] | None = None,
        unalias: bool = True,
        sort_collections: bool = False,
        adjust_cterm: Callable[[CTerm], CTerm] | None = None,
    ):
        super().__init__(
            definition,
            extra_unparsing_modules,
            patch_symbol_table,
            unalias,
            sort_collections,
        )
        self.adjust_cterm = adjust_cterm

    def show(
        self,
        cterm: CTerm,
        omit_config: bool = False,
        omit_constraints: bool = False,
        boolify: bool = False,
        minimize: bool = False,
    ) -> str:
        def _boolify(c: KInner) -> KInner:
            if type(c) is KApply and c.label.name == '#Equals' and c.args[0] == TRUE:
                return c.args[1]
            else:
                return c

        if self.adjust_cterm:
            cterm = self.adjust_cterm(cterm)

        if minimize:
            cterm = CTerm(minimize_term(cterm.config, keep_vars=free_vars(cterm.constraint)), cterm.constraints)

        if omit_constraints:
            cterm = CTerm(cterm.config)
        elif boolify:
            cterm = CTerm(cterm.config, map(_boolify, cterm.constraints))

        ret_strs = []
        if not omit_config:
            ret_strs.append(self.print(cterm.config))
        if not omit_constraints:
            ret_strs.extend([self.print(constraint) for constraint in cterm.constraints])
        if len(ret_strs) == 0:
            ret_strs = ['#Top']
        return '\n'.join(ret_strs)
